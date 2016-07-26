{-# LANGUAGE RankNTypes #-}
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
hoistVariables (CFunDef declspec declr decls body _) globals =
  let args = funDeclrNames declr
      env = initEnv (globals ++ args)
      (body', env') = runState (everywhereM' process body) env
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
  map identToString $ concat $ map (maybeToList . declToIdent) decls
derivedDeclrName _ = []

process :: Typeable a => a -> Env a
process = return `extM` processItem `extM` processStmt `extM` processExpr

processItem :: CBlockItem -> Env CBlockItem
processItem (CBlockDecl decl) = do
  started <- gets codeBegan
  if started
    then do
    initlist <- hoistDecl decl
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
  items' <- scope (everywhereM' process items)
  return $ CCompound labels (filter (not . emptyExprStmt) items') ni
processStmt (CFor first cond step stmt ni) = scope $ do
  first' <- case first of
    (Right decl) -> do
      exprs <- hoistDecl decl
      return $ case exprs of
        [] -> Left Nothing
        xs -> Left (Just (CComma xs undefNode))
    expr -> return expr
  return $ CFor first' cond step stmt ni
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

-- hoist declarations, returing a list of initializer expressions.
hoistDecl :: CDecl -> Env [CExpr]
hoistDecl (CDecl spec declrlist _) = do
  names' <- mapM (\d -> addDecl d True) [CDecl spec [(declr, Nothing, Nothing)] undefNode | (declr, _, Nothing) <- declrlist]
  declr' <- mapM declrToExpr (zip names' declrlist)
  return $ concat declr'

declrToExpr :: (String, (Maybe CDeclr, Maybe CInit, Maybe CExpr)) -> Env [CExpr]
declrToExpr (_, (_, Nothing, Nothing)) = return []
declrToExpr (name, (Just (CDeclr _ _ _ _ _), Just (CInitExpr expr _), Nothing)) = do
  let ident = internalIdent name
  return [CAssign CAssignOp (CVar ident undefNode) expr undefNode]
declrToExpr _ = error "unsupported initializer"

-- top-down variant of everywhereM, similar to everywhere'
everywhereM' :: Monad m => GenericM m -> GenericM m
everywhereM' f x = do
  x' <- f x
  gmapM (everywhereM' f) x'
