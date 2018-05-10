module Language.HigherRank.Parse
  ( parseExpr
  ) where

import           Data.Functor (($>))
import           Text.Megaparsec
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import           Text.Megaparsec.Expr
import           Data.Void
import           Data.Scientific (toRealFloat)

import           Language.HigherRank.Types


type Parser = Parsec Void String

parseExpr :: String -> Either String Expr
parseExpr s =
  case runParser (whole expr) "" s of
    Left err -> Left $ parseErrorPretty err
    Right e -> Right e

-- | Top-level parsers (should consume all input)
whole :: Parser a -> Parser a
whole p = sc *> p <* eof

------------------------------------------------------------------------
-- Expressions
------------------------------------------------------------------------

expr :: Parser Expr
expr = makeExprParser term pOperators

term :: Parser Expr
term = postfixChain factor fapp

fapp :: Parser (Expr -> Expr)
fapp = do
  e <- factor
  return (`EApp` e)

factor :: Parser Expr
factor = postfixChain atom colonOperator


colonOperator :: Parser (Expr -> Expr)
colonOperator = do
  colon
  t <- pType
  return (`EAnn` t)



atom :: Parser Expr
atom =
  choice
    [ try pLambda <|> pLambdaA
    -- , pIf
    , pLet
    , LitV <$> float
    -- , StrV <$> stringLiteral
    , topVal
    , trueVal
    , falseVal
    , evar <$> lidentifier
    -- , bconst
    , parens expr
    ]

-- bconst :: Parser Expr
-- bconst =
--   choice
--     [ rword "true" $> BoolV True
--     , rword "false" $> BoolV False
--     , rword "undefined" $> Bot
--     ]

pLambda :: Parser Expr
pLambda = do
  symbol "\\"
  xs <- some (lidentifier <|> symbol "_")
  symbol "->"
  e <- expr
  return $ foldr elam (elam (last xs) e) (init xs)

-- Annotated lambdas
pLambdaA :: Parser Expr
pLambdaA = do
  symbol "\\"
  xs <- parens tparam
  symbol "->"
  e <- expr
  return $ elamA  xs e

-- x : A
tparam :: Parser (String, Type)
tparam = do
  l <- lidentifier
  colon
  e <- pType
  return (l, e)

pLet :: Parser Expr
pLet = do
  rword "let"
  n <- lidentifier
  symbol "="
  e1 <- expr
  rword "in"
  e2 <- expr
  return $ elet n e1 e2


-- pIf :: Parser Expr
-- pIf = do
--   rword "if"
--   a <- expr
--   rword "then"
--   b <- expr
--   rword "else"
--   c <- expr
--   return $ If a b c


pOperators :: [[Operator Parser Expr]]
pOperators = [[InfixL (Add <$ symbol "+")]]


------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------

pType :: Parser Type
pType = makeExprParser atype tOperators

tOperators :: [[Operator Parser Type]]
tOperators = [[InfixR (TArr <$ symbol "->")]]

atype :: Parser Type
atype =
  choice
    [pForall, tvar <$> uidentifier, tconst, parens pType]

pForall :: Parser Type
pForall = do
  rword "forall"
  xs <- some uidentifier
  symbol "."
  t <- pType
  return $ foldr tforall (tforall (last xs) t) (init xs)


tconst :: Parser Type
tconst =
  choice
    [ rword "Double" $> TNum
    , rword "Int" $> TNum
    , rword "?" $> TUnknown
    -- , rword "String" $> StringT
    -- , rword "Bool" $> BoolT
    , rword "()" $> TUnit
    , rword "Bool" $> TBool
    ]


------------------------------------------------------------------------
-- Misc
------------------------------------------------------------------------

sc :: Parser ()
sc = L.space space1 lineCmnt blockCmnt
  where
    lineCmnt  = L.skipLineComment "--"
    blockCmnt = L.skipBlockComment "{-" "-}"


lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser String
symbol = L.symbol sc

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

brackets :: Parser a -> Parser a
brackets = between (symbol "[") (symbol "]")

braces :: Parser a -> Parser a
braces = between (symbol "{") (symbol "}")

float :: Parser Double
float = lexeme (toRealFloat <$> L.scientific)

topVal :: Parser Expr
topVal = symbol "()" >> return EUnit

trueVal :: Parser Expr
trueVal = symbol "true" >> return ETrue

falseVal :: Parser Expr
falseVal = symbol "false" >> return EFalse

stringLiteral :: Parser String
stringLiteral = lexeme $ char '"' >> manyTill L.charLiteral (char '"')

semi :: Parser String
semi = symbol ";"

colon :: Parser String
colon = symbol ":"

comma :: Parser String
comma = symbol ","

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
rws =
  [ "if"
  , "then"
  , "else"
  , "let"
  , "letrec"
  , "in"
  , "type"
  , "defrec"
  , "forall"
  , "trait"
  , "new"
  , "Trait"
  , "main"
  , "inherits"
  , "undefined"
  , "Double"
  , "Int"
  , "String"
  , "Bool"
  , "true"
  , "false"
  , "Top"
  , "override"
  ]


identifier :: Parser Char -> Parser String
identifier s = (lexeme . try) (p >>= check)
  where
    p = (:) <$> s <*> many identChar
    check x =
      if x `elem` rws
        then fail $ "keyword " ++ show x ++ " cannot be an identifier"
        else return x

identChar :: Parser Char
identChar = alphaNumChar <|> oneOf "_#'%"

lidentifier :: Parser String
lidentifier = identifier lowerChar

uidentifier :: Parser String
uidentifier = identifier upperChar
