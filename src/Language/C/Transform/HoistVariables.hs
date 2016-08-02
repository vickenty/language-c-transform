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
import Data.Generics
import Language.C
import Control.Monad.State.Strict
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

data EnvData = EnvData
    { renameMap :: Map.Map String String
    , toDeclare :: [CDecl]
    , namesUsed :: Set.Set String
    , codeBegan :: Bool
    , noRecurse :: Bool
    }

type Env = State EnvData

initEnv :: [String] -> EnvData
initEnv globals = EnvData
  { renameMap = Map.empty
  , toDeclare = []
  , namesUsed = Set.fromList globals
  , codeBegan = False
  , noRecurse = False
  }

addDecl :: CDecl -> Bool -> Env [Ident]
addDecl decl rename = do
  decl' <- if rename
            then renameDecl decl
            else return decl
  let idents = declIdents decl'
  let names = map identToString idents
  modify $ \st -> st { toDeclare = (toDeclare st) ++ [ decl' ]
                     , namesUsed = foldr Set.insert (namesUsed st) names
                     }
  return idents

declIdents :: CDecl -> [Ident]
declIdents (CDecl _ items _) = map itemIdent items

itemIdent :: (Maybe CDeclr, Maybe CInit, Maybe CExpr) -> Ident
itemIdent (Just declr, _, _) = declrIdent declr
itemIdent item@(Nothing, _, _) = error ("declaration item without declarator: " ++ (show item))

declrIdent :: CDeclr -> Ident
declrIdent (CDeclr (Just ident) _ _ _ _) = ident
declrIdent decl = error ("unnamed declarators are not supported: " ++ (show decl))

renameDecl :: CDecl -> Env CDecl
renameDecl (CDecl specs items _) = do
  items' <- mapM renameItem items
  return $ CDecl specs items' undefNode

renameItem :: (Maybe CDeclr, Maybe CInit, Maybe CExpr)
           -> Env (Maybe CDeclr, Maybe CInit, Maybe CExpr)
renameItem (Just declr, initr, expr) = do
  declr' <- renameDeclr declr
  return (Just declr', initr, expr)
renameItem item@(Nothing, _, _) = return item

renameDeclr :: CDeclr -> Env CDeclr
renameDeclr (CDeclr Nothing _ _ _ _)
  = error "unnamed declarators are not supported"
renameDeclr (CDeclr (Just ident) derived literal attrs _) = do
  let name = identToString ident
  name' <- renameIdent name ""
  modify $ \st -> st { renameMap = Map.insert name name' (renameMap st) }
  return $ CDeclr (Just (internalIdent name')) derived literal attrs undefNode

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
hoistVariables (CFunDef declspec declr decls body _) globals =
  let args = funDeclrNames declr
      env = initEnv (globals ++ args)
      (body', env') = runState (process body) env
      declstmt = map CBlockDecl (toDeclare env')
  in
    CFunDef declspec declr decls (prependItems body' declstmt) undefNode

prependItems :: CStat -> [CBlockItem] -> CStat
prependItems (CCompound labels items ni) more = (CCompound labels (more ++ items) ni)
prependItems _ _ = error "can not prepend items to non compound statement"

funDeclrNames :: CDeclr -> [String]
funDeclrNames (CDeclr mident derived _ _ _) =
  (map identToString (maybeToList mident)) ++ (funDeclrParamNames derived)

funDeclrParamNames :: [CDerivedDeclr] -> [String]
funDeclrParamNames declrlist = concat $ map derivedDeclrName declrlist

derivedDeclrName :: CDerivedDeclr -> [String]
derivedDeclrName (CFunDeclr (Left idents) _ _) = map identToString idents
derivedDeclrName (CFunDeclr (Right (decls, _)) _ _) =
  map identToString $ concat $ map declIdents decls
derivedDeclrName _ = []

processAny :: Data a => a -> Env a
processAny = return `extM` processItem `extM` processStmt `extM` processExpr

process :: Data a => a -> Env a
process x =
  if typeOf x == typeOf undefNode || typeOf x == typeOf "" || typeOf x == typeOf (1::Int)
  then return x
  else do
    x' <- processAny x
    nr <- gets noRecurse
    modify $ \st -> st { noRecurse = False }
    if nr
      then return x'
      else gmapM process x'

processItem :: CBlockItem -> Env CBlockItem
processItem (CBlockDecl decl) = do
  started <- gets codeBegan
  if started
    then do
    initlist <- hoistDecl decl
    modify $ \st -> st { noRecurse = True }
    return $ case initlist of
      [] -> CBlockStmt (CExpr Nothing undefNode)
      [ one ] -> CBlockStmt (CExpr (Just one) undefNode)
      many -> CBlockStmt (CExpr (Just (CComma many undefNode)) undefNode)
    else do
    _ <- addDecl decl False
    return $ CBlockStmt (CExpr Nothing undefNode)
processItem (CBlockStmt stmt) = do
  modify $ \st -> st { codeBegan = True }
  return $ CBlockStmt stmt
processItem (CNestedFunDef _) = error "nested functions are not supported"

processStmt :: CStat -> Env CStat
processStmt (CCompound labels items ni) = do
  items' <- scope (process items)
  return $ CCompound labels (filter (not . emptyExprStmt) items') ni
processStmt (CFor first cond step stmt ni) = scope $ do
  first' <- case first of
    (Right decl) -> do
      exprs <- hoistDecl decl
      return $ case exprs of
        [] -> Left Nothing
        xs -> Left (Just (CComma xs undefNode))
    expr -> return expr
  cond' <- process cond
  step' <- process step
  stmt' <- process stmt
  modify $ \st -> st { noRecurse = True }
  return $ CFor first' cond' step' stmt' ni
processStmt s = return s

processExpr :: CExpr -> Env CExpr
processExpr (CVar ident ni) = do
  namemap <- gets renameMap
  let ident' = case Map.lookup (identToString ident) namemap of
        Nothing -> ident
        Just name -> internalIdent name
  return $ CVar ident' ni
processExpr e = return e

-- Return true if statement contains empty expression.
emptyExprStmt :: CBlockItem -> Bool
emptyExprStmt (CBlockStmt (CExpr Nothing _)) = True
emptyExprStmt _ = False

-- Hoist declarations, returing a list of initializer expressions.
hoistDecl :: CDecl -> Env [CExpr]
hoistDecl decl = do
    initrs <- mapM hoistDeclr (splitDecl decl)
    return $ catMaybes initrs

hoistDeclr :: (CDecl, Maybe CExpr) -> Env (Maybe CExpr)
hoistDeclr (decl, mexpr) = do
  ident <- addDecl decl True
  mexpr' <- process mexpr
  case ident of
    [ident'] -> return $ fmap (assignTo ident') mexpr'
    idents -> error $ "addDecl returned multiple identifiers: " ++ (show decl) ++ "\n" ++ (show idents)

splitDecl :: CDecl -> [(CDecl, Maybe CExpr)]
splitDecl (CDecl specs items _) = map (splitDeclItem specs) items

splitDeclItem :: [CDeclSpec]
              -> (Maybe CDeclr, Maybe CInit, Maybe CExpr)
              -> (CDecl, Maybe CExpr)
splitDeclItem specs (mdeclr, Nothing, Nothing)
  = (CDecl specs [(mdeclr, Nothing, Nothing)] undefNode, Nothing)
splitDeclItem specs (mdeclr, Just (CInitExpr expr _), Nothing)
  = (CDecl specs [(mdeclr, Nothing, Nothing)] undefNode, Just expr)
splitDeclItem specs (Just declr, Just (CInitList list _), Nothing)
  = if isArrayDeclr declr
    then splitArrayItem specs declr list
    else splitStructItem specs declr list
splitDeclItem _ (_, _, _) = error "unexpected AST structure"

isArrayDeclr :: CDeclr -> Bool
isArrayDeclr (CDeclr _ derive _ _ _) = any isArrayDerivedDeclr derive

isArrayDerivedDeclr :: CDerivedDeclr -> Bool
isArrayDerivedDeclr (CArrDeclr _ _ _) = True
isArrayDerivedDeclr _ = False

splitArrayItem :: [CDeclSpec] -> CDeclr -> CInitList -> (CDecl, Maybe CExpr)
splitArrayItem _specs declr _list
  = error ("array list initializers are not supported: " ++ (show $ pretty declr))

splitStructItem :: [CDeclSpec] -> CDeclr -> CInitList -> (CDecl, Maybe CExpr)
splitStructItem specs declr list
  = (CDecl specs [(Just declr, Nothing, Nothing)] undefNode,
     Just (CCompoundLit (CDecl specs [(Nothing, Nothing, Nothing)] undefNode)
           list undefNode))

assignTo :: Ident -> CExpr -> CExpr
assignTo ident expr = CAssign CAssignOp (CVar ident undefNode) expr undefNode
