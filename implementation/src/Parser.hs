module Parser where

import Data.Void
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Control.Monad.Combinators.Expr

import Syntax
import Control.Monad (void)

type Parser = Parsec Void String

parseExp :: String -> Either String Exp
parseExp s =
  case runParser (whole expr) "" s of
    Left err -> Left $ errorBundlePretty err
    Right e -> Right e

-- | Top-level parsers (should consume all input)
whole :: Parser a -> Parser a
whole p = sc *> p <* eof

------------------------------------------------------------------------
-- Expressions
------------------------------------------------------------------------

expr :: Parser Exp
expr = makeExprParser term pOperators

term :: Parser Exp
term = postfixChain factor (try tapp <|> fapp)

fapp :: Parser (Exp -> Exp)
fapp = do
  e <- factor
  return (`App` e)

tapp :: Parser (Exp -> Exp)
tapp = do
  symbol "@"
  t <- atype
  return (`TApp` t)

factor :: Parser Exp
factor = postfixChain atom annOperator

annOperator :: Parser (Exp -> Exp)
annOperator = do
  symbol "::"
  t <- pType
  return (`Ann` t)

atom :: Parser Exp
atom =
  choice
    [ pLambda
    , pTAbs
    , pCase
    , pFix
    , try pLet
    , pLetAnn
    , Var <$> identifier
    , ILit <$> signedInt
    , BLit <$> bool
    , Nil <$ symbol "[]"
    , parens expr
    ]

idBound :: Parser (String, Typ)
idBound = try explicit <|> implicit
  where
    implicit = do
      x <- identifier
      return (x, TTop)
    explicit = do
      symbol "("
      x <- identifier
      symbol "<:"
      t <- pType
      symbol ")"
      return (x, t)

pLambda :: Parser Exp
pLambda = do
  symbol "\\"
  x <- identifier
  symbol "->"
  Lam x <$> expr

pFix :: Parser Exp
pFix = do
  rword "fix"
  Fix <$> expr

pTAbs :: Parser Exp
pTAbs = do
  symbol "/\\"
  (x, t) <- idBound
  symbol "."
  TAbs x t <$> expr

pCase :: Parser Exp
pCase = do
  rword "case"
  e <- expr
  rword "of"
  symbol "[]"
  symbol "->"
  e1 <- expr
  symbol ";"
  symbol "("
  x <- identifier
  symbol ":"
  xs <- identifier
  symbol ")"
  symbol "->"
  Case e e1 . Lam x . Lam xs <$> expr

pLetAnn :: Parser Exp
pLetAnn = do
  rword "let"
  x <- identifier
  symbol "::"
  t <- pType
  symbol "="
  e1 <- expr
  rword "in"
  LetA x t e1 <$> expr

pLet :: Parser Exp
pLet = do
  rword "let"
  x <- identifier
  symbol "="
  e1 <- expr
  rword "in"
  Let x e1 <$> expr

pOperators :: [[Operator Parser Exp]]
pOperators = [[InfixR (Cons <$ symbol ":")]]

------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------

pType :: Parser Typ
pType = makeExprParser atype tOperators

tOperators :: [[Operator Parser Typ]]
tOperators = [[InfixR (TArr <$ symbol "->")]]

atype :: Parser Typ
atype =
  choice
    [pForall, TVar <$> identifier, tconst, listType, parens pType]

pForall :: Parser Typ
pForall = do
  rword "forall"
  (x, t) <- idBound
  symbol "."
  Forall x t <$> pType

tconst :: Parser Typ
tconst =
  choice
    [ TInt  <$ rword "Int"
    , TBool <$ rword "Bool"
    , TTop  <$ rword "Top"
    , TBot  <$ rword "Bot"]

listType :: Parser Typ
listType = do
  symbol "["
  t <- pType
  symbol "]"
  return $ TList t

------------------------------------------------------------------------
-- Misc
------------------------------------------------------------------------

sc :: Parser ()
sc = L.space space1 empty empty

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser ()
symbol = void . L.symbol sc

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

brackets :: Parser a -> Parser a
brackets = between (symbol "[") (symbol "]")

int :: Parser Integer
int = lexeme L.decimal

signedInt :: Parser Integer
signedInt = L.signed sc int

bool :: Parser Bool
bool =
  choice
    [ True  <$ rword "True"
    , False <$ rword "False"]

rword :: String -> Parser ()
rword w = string w *> notFollowedBy alphaNumChar *> sc

postfixChain :: Parser a -> Parser (a -> a) -> Parser a
postfixChain p op = do
  x <- p
  rest x
  where
    rest x =
      (do f <- op
          rest $ f x) <|>
      return x

rws :: [String] -- list of reserved words
rws = ["forall", "case", "of", "fix", "let", "in", "True", "False"]

identifier :: Parser String
identifier = (lexeme . try) (p >>= check)
  where
    p = (:) <$> lowerChar <*> many identChar
    check x =
      if x `elem` rws
        then fail $ "keyword " ++ show x ++ " cannot be an identifier"
        else return x

identChar :: Parser Char
identChar = alphaNumChar <|> oneOf "_'"