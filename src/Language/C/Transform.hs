module Language.C.Transform (transform) where

import Language.C
import Language.C.Data.Ident
import Control.Monad.State.Lazy
import Language.C.Transform.HoistVariables

type Env = State [String]

transform :: CTranslUnit -> IO CTranslUnit
transform (CTranslUnit defs info) = do
  let transformed = evalState (mapM transformDef defs) []
  return $ CTranslUnit transformed info

transformDef :: CExtDecl -> Env CExtDecl
transformDef (CFDefExt fundef@(CFunDef _ declarator _ _ _)) = do
  _ <- addDeclr declarator
  env <- get
  return $ CFDefExt (hoistVariables fundef env)
transformDef declext@(CDeclExt decl) = do
  addDecl decl
  return declext
transformDef def = return def

addIdent :: Ident -> Env ()
addIdent (Ident ident _ _) = do
  modify $ \st -> ident : st
  return ()

addDeclr :: CDeclr -> Env ()
addDeclr (CDeclr (Just ident) _ _ _ _) = addIdent ident
addDeclr _ = return ()

addDecl :: CDecl -> Env ()
addDecl (CDecl specifiers items _) = do
  _ <- mapM addSpec specifiers
  _ <- mapM addItem items
  return ()
  where
    addItem (Just declr, _, _) = addDeclr declr
    addItem _ = return ()

    addSpec (CTypeSpec typespec) = addType typespec
    addSpec _ = return ()

    addType (CEnumType enumspec _) = addEnum enumspec
    addType _ = return ()

    addEnum (CEnum _ (Just enumrs) _ _) = do
      _ <- mapM addEnumr enumrs
      return ()
    addEnum _ = return ()

    addEnumr (ident, _) = addIdent ident
