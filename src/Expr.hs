module Expr where

import Types
import qualified TyCoRep as T
import qualified DataCon as D
import qualified GhcPlugins as Core
import CoreUtils as Utils
import Control.Monad
import Data.Char
import Text.Parsec
import qualified Text.Parsec.Token as P
import Data.List
import Text.Parsec.Language

type Module = [(String, SortScheme, Expr)]

-- Add range information and parent expr
data Expr =
    ECst String
  | ECon String
  | EVar String [Sort]
  | EAbs String Sort Expr
  | EApp Expr Expr
  | ECase Expr String Sort Sort [Alt]
  | ELet [(String, SortScheme, Expr)] Expr

  | AltExpr Alt -- Only used in errors

-- Literal cases
data Alt =
    ACon String [String] Expr
  | ALit String Expr
  | Default Expr

notDef :: Alt -> Bool
notDef (ALit _ _) = True
notDef _ = False

instance Show Expr where
  show (ECst s) = s
  show (ECon k) = k
  show (EVar v []) = v
  show (EVar v ts) = v ++ show ts
  show (EAbs s ts e) = "(\\" ++ s ++ ":" ++ show ts ++ "." ++ show e ++ ")"
  show (EApp e1 e2) = "(" ++ show e1 ++ " " ++ show e2 ++ ")"
  show (ECase e b _ t alts) = "(case " ++ show e ++ " as " ++ show b ++ " return " ++ show t ++ " of {" ++ concatMap (show . AltExpr) alts ++ "})"
  show (ELet xs e2) = "(let " ++ (concatMap (\(x, t, e1) -> show x ++ ":" ++ show t ++ " = " ++ show e1 ++ ";") xs)++ " in " ++ show e2 ++ ")"

  show (AltExpr a) = show a

instance Show Alt where
  show (ACon k args e) = k ++ " " ++ intercalate " " args ++ " -> " ++ show e
  show (ALit s e) = show s ++ "->" ++ show e
  show (Default e) = "otherwise -> " ++ show e

name :: Core.NamedThing n => n -> String
name = Core.nameStableString . Core.getName

getTypeScheme :: Core.CoreExpr -> SortScheme
getTypeScheme = fromCoreTypeScheme . Utils.exprType

fromCoreType :: T.Type -> Sort
fromCoreType (T.TyVarTy a) = SVar (name a)
fromCoreType (T.FunTy t1 t2) = SArrow (fromCoreType t1) (fromCoreType t2)
fromCoreType (T.TyConApp tc t2)= let n = name tc in
  if isPrefixOf "$ghc-prim$GHC.Types$" n
    then SBase n
    else SData (name tc)
fromCoreType _ = error "Unimplemented"

getBinds :: [(Core.Var, Core.CoreExpr)] -> [(String, SortScheme, Expr)]
getBinds [] = []
getBinds ((v, e):bs) = let
  bs' = getBinds bs
  b'  = (name v, getTypeScheme e, fromCoreExpr e)
  in b':bs'

fromCoreTypeScheme :: T.Type -> SortScheme
fromCoreTypeScheme (T.ForAllTy b t) = let
  SForall as t' = fromCoreTypeScheme t
  in SForall ((name $ T.binderVar b):as) t'
fromCoreTypeScheme t1 = SForall [] $ fromCoreType t1

fromAlts :: Core.Alt Core.CoreBndr -> Alt
fromAlts (Core.DataAlt d, bs, e) = ACon (name d) (fmap name bs) (fromCoreExpr e)
fromAlts (Core.DEFAULT, [], e) = Default (fromCoreExpr e)
fromAlts (Core.LitAlt l, [] , e) = ALit (fromLiteral l) (fromCoreExpr e)

fromLiteral :: Core.Literal -> String
fromLiteral = undefined

fromCoreExpr :: Core.CoreExpr -> Expr
fromCoreExpr (Core.Lit l) = ECst (fromLiteral l)
fromCoreExpr t
  | isVar t = fromVarAtType t
fromCoreExpr (Core.App e1 e2) = EApp (fromCoreExpr e1) (fromCoreExpr e2)
fromCoreExpr (Core.Let (Core.NonRec i e1) e2) = ELet [(name i, getTypeScheme e1, (fromCoreExpr e1))] (fromCoreExpr e2)
fromCoreExpr (Core.Let (Core.Rec bs) e2) = ELet (getBinds bs) (fromCoreExpr e2)
fromCoreExpr (Core.Case e b rt as) = ECase (fromCoreExpr e) (name b) (fromCoreType $ Core.varType b) (fromCoreType rt) (fmap fromAlts as)
fromCoreExpr (Core.Tick _ e) = fromCoreExpr e
fromCoreExpr (Core.Lam b e1) = EAbs (name b) (fromCoreType $ Core.varType b) (fromCoreExpr e1)

fromCoreExpr (Core.Cast _ _) = error "Unimplemented"
fromCoreExpr (Core.Coercion _) = error "Unimplemented"
fromCoreExpr _ = error "Unimplemented"

isVar :: Core.CoreExpr -> Bool
isVar (Core.Var _) = True
isVar (Core.App e1 (Core.Type _)) = isVar e1
isVar _ = False

fromVarAtType :: Core.CoreExpr -> Expr
fromVarAtType (Core.Var i) = EVar (name i) []
fromVarAtType (Core.App e1 (Core.Type t)) = let
  (EVar n ts) = fromVarAtType e1
  in EVar n (fromCoreType t:ts)

type Parser = Parsec String ()

pExpr :: Parser Expr
pExpr = chainl1 pNonApp $ return EApp

pNonApp :: Parser Expr
pNonApp = parens pExpr <|> pCase <|> pVar <|> pCon <|> pAbs <|> pLet <|> pCst

pCst :: Parser Expr
pCst = ECst <$> show <$> natural

pLet :: Parser Expr
pLet = do
  try $ reserved "let"
  xs <- many pIn
  reserved "in"
  e2 <- pExpr
  return $ ELet xs e2

pIn :: Parser (String, SortScheme, Expr)
pIn = do
  x <- pVarName
  symbol ":"
  t <- try pScheme <|> (SForall []) <$> pType
  symbol "="
  e1 <- pExpr
  symbol ";"
  return (x, t, e1)

pBase :: Parser Sort
pBase = do
  reserved "Int"
  return $ SBase "Int"

pVarName :: Parser String
pVarName = try (symbol "_") <|> do
  name <- identifier
  guard $ isLower $ head name
  return name

pConName :: Parser String
pConName = do
  name <- identifier
  guard $ isUpper $ head name
  return name

pVar :: Parser Expr
pVar = do
  name <- try $ pVarName
  args <- many $ brackets (many pType)
  return $ EVar name (concat args)

pCon :: Parser Expr
pCon = ECon <$> pConName

pType :: Parser Sort
pType = chainr1 pNonArr (symbol "->" *> return SArrow)

pNonArr :: Parser Sort
pNonArr = parens pType <|> try pBase <|> SVar <$> try pVarName <|> SData <$> pConName

pScheme :: Parser SortScheme
pScheme = do
  try $ reserved "forall"
  name <- pVarName
  symbol "."
  SForall as t <- try pScheme <|> (SForall []) <$> pType
  return $ SForall (name:as) t

pAbs :: Parser Expr
pAbs = do
  try $ symbol "\\"
  name <- pVarName
  symbol ":"
  t <- pType
  symbol "."
  body <- pExpr
  return $ EAbs name t body

pCase :: Parser Expr
pCase = do
  try $ reserved "case"
  e <- pExpr
  reserved "as"
  n <- pVarName
  symbol ":"
  et <- pType
  reserved "return"
  rt <- pType
  reserved "of"
  symbol "{"
  alts <- many (try pDefault <|> pAlts)
  symbol "}"
  return $ ECase e n et rt alts

pDefault :: Parser Alt
pDefault = do
  try $ reserved "otherwise"
  symbol "->"
  e <- pExpr
  symbol ";"
  return $ Default e

pAlts :: Parser Alt
pAlts = do
  k <- pConName
  xs <- many pVarName
  symbol "->"
  e <- pExpr
  symbol ";"
  return $ ACon k xs e

lexer       = P.makeTokenParser haskellStyle { P.reservedNames  = ["Int", "let","in","case","of", "default", "return", "as"] }
natural     = P.natural lexer
parens      = P.parens lexer
brackets    = P.brackets lexer
symbol      = P.symbol lexer
identifier  = P.identifier lexer
reserved    = P.reserved lexer
