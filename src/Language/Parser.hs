module Language.Parser (Parse(..), lexParse) where

import Prelude hiding (foldr1)
import Data.Text (pack)
import Data.List.NonEmpty qualified as NonEmpty
import Data.Foldable1
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Data.Set qualified as Set
import Prettyprinter.Utils

import Base hiding (brackets, sep)
import Language.Type
import Language.Expr
import Language.Declaration

type Lexer = Parsec Void Text

data Lexeme
  = Keyword Text
  | Identifier Text
  | Constructor Text
  | Operator Text
  | Separator Text
  | Bracket Bracket
  | Underscore
  | IntLit Int
  | StringLit String
  | Newline Int
  deriving (Eq, Ord, Show, Read)

type Bracket = (Shape, Position)

data Shape = Fancy | Round | Curly | Square
  deriving (Eq, Ord, Show, Read)

data Position = Open | Close
  deriving (Eq, Ord, Show, Read)

sc :: Lexer ()
sc = L.space hspace1 (L.skipLineComment "--") empty

sc' :: Lexer ()
sc' = L.space mzero (L.skipLineComment "--") empty

comment :: Lexer ()
comment = L.skipLineComment "--"

identChar :: Lexer Char
identChar = alphaNumChar <|> char '_' <|> char '\''

keywords :: [Text]
keywords = ["forall", "inl", "inr"]

ident :: Lexer Char -> Lexer Text
ident start = fmap pack $ (:) <$> start <*> many identChar

identOrKeyword :: Lexer Lexeme
identOrKeyword = ident (lowerChar <|> char '_') <&> \case
  t | t `elem` keywords -> Keyword t
    | otherwise -> Identifier t

operator :: Lexer Text
operator = fmap pack . some . choice . fmap char $
  ("!$%&*+-.:<=>\\^|" :: String)

separator :: Lexer Text
separator = string "," <|> string ";"

bracket :: Lexer Bracket
bracket = choice
  [ (Fancy , Open) <$ string "{-#", (Fancy , Close) <$ string "#-}"
  , (Round , Open) <$ char   '('  , (Round , Close) <$ char     ')'
  , (Curly , Open) <$ char   '{'  , (Curly , Close) <$ char     '}'
  , (Square, Open) <$ char   '['  , (Square, Close) <$ char     ']'
  ]

intLit :: Lexer Int
intLit = read <$> some digitChar

stringLit :: Lexer String
stringLit = char '"' >> manyTill L.charLiteral (char '"')

lex :: Lexer [Lexeme]
lex = (optional comment *>) . many . choice $ fmap (L.lexeme sc)
  [ identOrKeyword
  , Constructor <$> ident upperChar
  , Operator <$> operator
  , Separator <$> separator
  , Bracket <$> bracket
  , Underscore <$ char '_'
  , IntLit <$> intLit
  , StringLit <$> stringLit
  ] ++ [ L.lexeme sc' $ Newline . length <$ eol <*> many (char ' ') ]

type Parser = Parsec Void [Lexeme]

brackets :: Shape -> Parser a -> Parser a
brackets sh = between
  (single $ Bracket (sh, Open))
  (single $ Bracket (sh, Close))

alt :: Parser a -> Parser b -> Parser [a]
alt p q = NonEmpty.toList <$> alt1 p q <|> mempty

alt1 :: Parser a -> Parser b -> Parser (NonEmpty a)
alt1 p q = (:|) <$> p <*> many (q *> p)

parseList :: Shape -> Parser a -> Parser [a]
parseList b p = brackets b (alt p (sep ","))

identifier :: Parser Text
identifier = flip token Set.empty \case
  Identifier i -> Just i
  _ -> Nothing

int :: Parser Int
int = flip token Set.empty \case
  IntLit i -> Just i
  _ -> Nothing

num :: Int -> Parser Int
num n = do
  i <- int
  guard $ i == n
  return i

sep :: Text -> Parser Lexeme
sep = single . Separator

op :: Text -> Parser Lexeme
op = single . Operator

key :: Text -> Parser Lexeme
key = single . Keyword

ctr :: Text -> Parser Lexeme
ctr = single . Constructor

class Parse a where
  parser :: Parser a

lexParse :: Parser a -> Text -> Maybe a
lexParse p t = parseMaybe Language.Parser.lex t >>= parseMaybe p

instance Parse Base where
  parser = choice
    [ Int  <$ ctr "Int"
    , Bool <$ ctr "Bool"
    ]

instance Parse Constraint where
  parser = choice
    [ Eq  <$ ctr "Eq"  <*> identifier
    , Ord <$ ctr "Ord" <*> identifier
    ]

sums :: Parser Mono
sums = foldr1 Sum <$> alt1 products (op "+")

products :: Parser Mono
products = foldr1 Tup <$> alt1 mono (op "*")

mono :: Parser Mono
mono = choice
  [ Free <$> identifier
  , Top <$ num 1
  , List <$> brackets Square parser
  , Base <$> parser
  , brackets Round sums
  ]

instance Parse Mono where
  parser = sums

instance Parse Signature where
  parser = do
    vars <- choice
      [ key "forall" *> many identifier <* op "."
      , mempty
      ]
    constraints <- choice
      [ parseList Round parser <* op "=>"
      , (:[]) <$> parser <* op "=>"
      , mempty
      ]
    context <- choice
      [ parseList Curly ((,) <$> identifier <* op ":" <*> parser) <* op "->"
      , mempty
      ]
    goal <- parser
    return Signature { vars, constraints, context, goal }

instance Parse (Named Signature) where
  parser = Named <$> identifier <* op ":" <*> parser

instance Parse Lit where
  parser = choice
    [ MkBool False <$ ctr "False"
    , MkBool True  <$ ctr "True"
    , MkInt <$> int
    ]

instance Parse h => Parse (Expr h) where
  parser = choice
    [ Unit <$ op "-"
    , brackets Round do
      x <- parser
      optional (sep "," *> parser) >>= \case
        Nothing -> return x
        Just y -> return $ Pair x y
    , Inl <$ key "inl" <*> parser
    , Inr <$ key "inr" <*> parser
    , Lst <$> parseList Square parser
    , Lit <$> parser
    , Hole <$> brackets Curly parser
    ]

spacedExprUntil :: Parse h => Lexeme -> Parser [Expr h]
spacedExprUntil l = many $ choice
  [ brackets Round parser
  , Lst <$> parseList Square parser
  , do
    x <- anySingleBut l
    maybe mzero return $ parseMaybe parser [x]
  ]

instance Parse Example where
  parser = do
    inputs <- spacedExprUntil (Operator "->")
    output <- optional (op "->" *> parser)
    case (inputs, output) of
      ([out], Nothing ) -> return $ Example [] out
      (_:_  , Just out) -> return $ Example inputs out
      _ -> mzero

instance Parse (Named Example) where
  parser = Named <$> identifier <*> do
    Example <$> spacedExprUntil (Operator "=") <* op "=" <*> parser

instance Parse Problem where
  parser = do
    Named "_" p <- parser
    return p

instance Parse (Named Problem) where
  parser = do
    Named name signature <- parser
    _ <- single (Newline 0)
    bs <- alt1 parser (single $ Newline 0)
    bindings <- NonEmpty.toList <$> forM bs \(Named name' b) -> do
      guard $ name == name'
      return b
    return $ Named name Declaration { signature, bindings }

instance Parse Void where
  parser = mzero
