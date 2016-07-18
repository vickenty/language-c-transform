-- |
-- Module: Language.C.Transform.HoistVariables
-- Description: Move variable declarations to the top of the function
-- Copyright: Vickenty Fesunov, 2016
-- License: BSD
-- Stability: experimental
--
-- Move variable declarations to the top of the function.

module Language.C.Transform.HoistVariables (hoistVariables) where
import Data.Maybe
import Language.C
import Control.Monad.State.Lazy
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

data EnvData = EnvData
    { renameMap :: Map.Map String String
    , toDeclare :: [CDecl]
    , namesUsed :: Set.Set String
    , codeBegan :: Bool
    }

type Env = State EnvData

initEnv :: [String] -> EnvData
initEnv globals = EnvData
  { renameMap = Map.empty
  , toDeclare = []
  , namesUsed = Set.fromList globals
  , codeBegan = False
  }

declToIdent :: CDecl -> Maybe Ident
declToIdent (CDecl _ [(Just (CDeclr mident _ _ _ _), _, _)] _) = mident
declToIdent (CDecl _ [] _) = Nothing
declToIdent decl = error ("compound declarations are not supported: " ++ (show decl))

addDecl :: CDecl -> Bool -> Env String
addDecl decl rename = do
  let mname = fmap identToString $ declToIdent decl
  case mname of
    Just name -> do
      name' <- if rename
               then renameIdent name ""
               else return name
      let decl' = renameDecl name' decl
      modify $ \st -> st { toDeclare = (toDeclare st) ++ [ decl' ]
                         , renameMap = Map.insert name name' (renameMap st)
                         , namesUsed = Set.insert name' (namesUsed st)
                         }
      return name'
    Nothing -> return ""

renameIdent :: String -> String -> Env String
renameIdent name suffix = do
  used <- gets namesUsed
  let name' = if suffix == "" then name else (name ++ "_" ++ suffix)
  if Set.member name' used
    then renameIdent name (next suffix)
    else return name'
  where
    next "" = "2"
    next s = show (1 + (read s::Int))

renameDecl :: String -> CDecl -> CDecl
renameDecl name (CDecl spec [(declr, initr, expr)] ni) =
  let declr' = fmap (renameDeclr name) declr in
  CDecl spec [(declr', initr, expr)] ni
renameDecl _ _ = error "multiple declarations are not supported yet"

renameDeclr :: String -> CDeclr -> CDeclr
renameDeclr name (CDeclr _ derived literal attr ni) =
  CDeclr (Just (internalIdent name)) derived literal attr ni

scope :: Env a -> Env a
scope env = do
  old <- (gets renameMap)
  a' <- env
  modify $ \st -> st { renameMap = old }
  return a'

-- | Perform hoisting on a function definition.
--
-- Moves local variable declarations to the top of the function, so that occur
-- before the first statement. Variables are renamed to avoid name and type
-- conflicts between variables coming from different scopes. Variables that only
-- temporarily shadow a global identifier or a function argument are renamed as
-- well.
--
-- For example, given a function definition for:
--
-- > int func(long foo) {
-- >   int bar;
-- >   if (foo < 0) {
-- >     char * bar = "Hello";
-- >   } else {
-- >     int foo = 1;
-- >     int baz = foo;
-- >   }
-- > }
--
-- and a list of globals @["bar", "baz"]@ the resulting function definition will be:
--
-- > int func(long foo) {
-- >   int bar;
-- >   char * bar_2;
-- >   int foo_2;
-- >   int baz_2;
-- >   if (foo < 0) {
-- >     bar_2 = "Hello";
-- >   } else {
-- >     foo_2 = 1;
-- >     baz_2 = foo_2;
-- >   }
-- > }
hoistVariables :: CFunDef -> [String] -> CFunDef
hoistVariables (CFunDef declspec declr decls (CCompound [] items _) _) globals =
  let args = funDeclrNames declr
      env = initEnv (globals ++ args)
      (items', env') = runState (concatM $ mapM processItem items) env
      declstmt = map CBlockDecl (toDeclare env')
      body' = CCompound [] (declstmt ++ items') undefNode
  in
    CFunDef declspec declr decls body' undefNode
  where concatM = liftM concat
hoistVariables _ _ = error "unsupported function definition structure"

funDeclrNames :: CDeclr -> [String]
funDeclrNames (CDeclr mident derived _ _ _) =
  (map identToString (maybeToList mident)) ++ (funDeclrParamNames derived)

funDeclrParamNames :: [CDerivedDeclr] -> [String]
funDeclrParamNames declrlist = concat $ map derivedDeclrName declrlist

derivedDeclrName :: CDerivedDeclr -> [String]
derivedDeclrName (CFunDeclr (Left idents) _ _) = map identToString idents
derivedDeclrName (CFunDeclr (Right (decls, _)) _ _) =
  map identToString $ concat $ map (maybeToList . declToIdent) decls
derivedDeclrName _ = []

processItem :: CBlockItem -> Env [CBlockItem]
processItem (CBlockDecl decl) = do
  started <- gets codeBegan
  if started
    then do
    initlist <- hoistDecl decl
    return $ case initlist of
      [] -> []
      [ one ] -> [CBlockStmt (CExpr (Just one) undefNode)]
      many -> [CBlockStmt (CExpr (Just (CComma many undefNode)) undefNode)]
    else do
    _ <- addDecl decl False
    return []
processItem (CBlockStmt stmt) = do
  modify $ \st -> st { codeBegan = True }
  stmt' <- processStmt stmt
  return $ [ CBlockStmt stmt' ]
processItem (CNestedFunDef _) = error "nested functions are not supported"

processStmt :: CStat -> Env CStat
processStmt (CLabel label stmt attr ni) = do
  stmt' <- processStmt stmt
  return $ CLabel label stmt' attr ni
processStmt (CCase expr stmt ni) = do
  expr' <- processExpr expr
  stmt' <- processStmt stmt
  return $ CCase expr' stmt' ni
processStmt (CCases lower upper stmt ni) = do
  lower' <- processExpr lower
  upper' <- processExpr upper
  stmt' <- processStmt stmt
  return $ CCases lower' upper' stmt' ni
processStmt (CDefault stmt ni) = do
  stmt' <- processStmt stmt
  return $ CDefault stmt' ni
processStmt (CExpr mexpr ni) = do
  expr' <- mapM processExpr mexpr
  return $ CExpr expr' ni
processStmt (CCompound labels items ni) = do
  items' <- scope (mapM processItem items)
  return $ CCompound labels (concat items') ni
processStmt (CIf expr thenstmt melsestmt ni) = do
  expr' <- processExpr expr
  thenstmt' <- processStmt thenstmt
  melsestmt' <- mapM processStmt melsestmt
  return $ CIf expr' thenstmt' melsestmt' ni
processStmt (CSwitch expr stmt ni) = do
  expr' <- processExpr expr
  stmt' <- processStmt stmt
  return $ CSwitch expr' stmt' ni
processStmt (CWhile expr stmt isDo ni) = do
  expr' <- processExpr expr
  stmt' <- processStmt stmt
  return $ CWhile expr' stmt' isDo ni
processStmt (CFor first cond step stmt ni) = do
  first' <- case first of
    (Right decl) -> do
      exprs <- hoistDecl decl
      return $ case exprs of
        [] -> Left Nothing
        xs -> Left (Just (CComma xs undefNode))
    (Left mexpr) -> do
      mexpr' <- mapM processExpr mexpr
      return $ Left mexpr'
  cond' <- mapM processExpr cond
  step' <- mapM processExpr step
  stmt' <- processStmt stmt
  return $ CFor first' cond' step' stmt' ni
processStmt stmt@(CGoto _ _) = return stmt
processStmt (CGotoPtr _ _) = error "goto expression is not supported"
processStmt stmt@(CCont _) = return stmt
processStmt stmt@(CBreak _) = return stmt
processStmt (CReturn mexpr ni) = do
  mexpr' <- mapM processExpr mexpr
  return $ CReturn mexpr' ni
processStmt (CAsm _ _) = error "inline assembly is not supported"

processExpr :: CExpr -> Env CExpr
processExpr (CComma exprs ni) = do
  exprs' <- mapM processExpr exprs
  return $ CComma exprs' ni
processExpr (CAssign op lexpr rexpr ni) = do
  lexpr' <- processExpr lexpr
  rexpr' <- processExpr rexpr
  return $ CAssign op lexpr' rexpr' ni
processExpr (CCond ex1 ex2 ex3 ni) = do
  ex1' <- processExpr ex1
  ex2' <- mapM processExpr ex2
  ex3' <- processExpr ex3
  return $ CCond ex1' ex2' ex3' ni
processExpr (CBinary op ex1 ex2 ni) = do
  ex1' <- processExpr ex1
  ex2' <- processExpr ex2
  return $ CBinary op ex1' ex2' ni
processExpr (CCast decl ex ni) = do
  ex' <- processExpr ex
  return $ CCast decl ex' ni
processExpr (CUnary op ex ni) = do
  ex' <- processExpr ex
  return $ CUnary op ex' ni
processExpr (CSizeofExpr ex ni) = do
  ex' <- processExpr ex
  return $ CSizeofExpr ex' ni
processExpr e@(CSizeofType _ _) = return e
processExpr (CAlignofExpr ex ni) = do
  ex' <- processExpr ex
  return $ CAlignofExpr ex' ni
processExpr e@(CAlignofType _ _) = return e
processExpr (CComplexReal ex ni) = do
  ex' <- processExpr ex
  return $ CComplexReal ex' ni
processExpr (CComplexImag ex ni) = do
  ex' <- processExpr ex
  return $ CComplexImag ex' ni
processExpr (CIndex ex1 ex2 ni) = do
  ex1' <- processExpr ex1
  ex2' <- processExpr ex2
  return $ CIndex ex1' ex2' ni
processExpr (CCall ex1 ex2 ni) = do
  ex1' <- processExpr ex1
  ex2' <- mapM processExpr ex2
  return $ CCall ex1' ex2' ni
processExpr (CMember ex ident flag ni) = do
  ex' <- processExpr ex
  return $ CMember ex' ident flag ni
processExpr (CVar ident ni) = do
  namemap <- gets renameMap
  let ident' = case Map.lookup (identToString ident) namemap of
        Nothing -> ident
        Just name -> internalIdent name
  return $ CVar ident' ni
processExpr e@(CConst _) = return e
processExpr e@(CCompoundLit _ _ _) = return e
processExpr (CStatExpr stmt ni) = do
  stmt' <- processStmt stmt
  return $ CStatExpr stmt' ni
processExpr (CLabAddrExpr _ _) = error "label address expression is not supported"
processExpr e@(CBuiltinExpr _) = return e

-- hoist declarations, returing a list of initializer expressions.
hoistDecl :: CDecl -> Env [CExpr]
hoistDecl (CDecl spec declrlist _) = do
  names' <- mapM (\d -> addDecl d True) [CDecl spec [(declr, Nothing, Nothing)] undefNode | (declr, _, Nothing) <- declrlist]
  declr' <- mapM declrToExpr (zip names' declrlist)
  return $ concat declr'

declrToExpr :: (String, (Maybe CDeclr, Maybe CInit, Maybe CExpr)) -> Env [CExpr]
declrToExpr (_, (_, Nothing, Nothing)) = return []
declrToExpr (name, (Just (CDeclr _ _ _ _ _), Just (CInitExpr expr _), Nothing)) = do
  expr' <- processExpr expr
  let ident = internalIdent name
  return [CAssign CAssignOp (CVar ident undefNode) expr' undefNode]
declrToExpr _ = error "unsupported initializer"
