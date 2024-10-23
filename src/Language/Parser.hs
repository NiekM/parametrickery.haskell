{-# LANGUAGE UndecidableInstances #-}

module Language.Parser (Parse(..), lexParse, test) where

import Prelude hiding (foldr1)
import Data.Text (pack)
import Data.List.NonEmpty qualified as NonEmpty
import Text.Megaparsec
import Text.Megaparsec.Char hiding (newline)
import qualified Text.Megaparsec.Char.Lexer as L
import Data.Set qualified as Set

import Base hiding (some, many)
import Language.Type
import Language.Expr
import Language.Problem

type Lexer = Parsec Void Text

data Lexeme
  = Keyword Text
  | Identifier Text
  | Constr Text
  | Operator Text
  | Separator Text
  | Bracket Bracket
  | Underscore
  | IntLit Int
  | StringLit String
  | Newline Int
  deriving stock (Eq, Ord, Show, Read)

type Bracket = (Shape, Position)

data Shape = Fancy | Round | Curly | Square
  deriving stock (Eq, Ord, Show, Read)

data Position = Open | Close
  deriving stock (Eq, Ord, Show, Read)

sc :: Lexer ()
sc = L.space hspace1 (L.skipLineComment "--") empty

sc' :: Lexer ()
sc' = L.space empty (L.skipLineComment "--") empty

comment :: Lexer ()
comment = L.skipLineComment "--"

identChar :: Lexer Char
identChar = alphaNumChar <|> char '_' <|> char '\''

keywords :: [Text]
keywords = []

ident :: Lexer Char -> Lexer Text
ident start = fmap pack $ (:) <$> start <*> many identChar

identOrKeyword :: Lexer Lexeme
identOrKeyword = ident (lowerChar <|> char '_') <&> \case
  t | t `elem` keywords -> Keyword t
    | otherwise -> Identifier t

operator :: Lexer Text
operator = fmap pack . some . choice . fmap char $
  ("!$%&*+-.:<=>\\^" :: String)

separator :: Lexer Text
separator = string "," <|> string ";" <|> string "|"

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
  , Constr <$> ident upperChar
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

statementSep :: Parser Lexeme
statementSep = newline 0 <|> sep ";"

identifier :: Parser Name
identifier = Name <$> flip token Set.empty \case
  Identifier i -> Just i
  _ -> Nothing

constructor :: Parser Name
constructor = Name <$> flip token Set.empty \case
  Constr i -> Just i
  _ -> Nothing

int :: Parser Int
int = flip token Set.empty \case
  IntLit i -> Just i
  _ -> Nothing

sep :: Text -> Parser Lexeme
sep = single . Separator

op :: Text -> Parser Lexeme
op = single . Operator

ctr :: Text -> Parser Lexeme
ctr = single . Constr

newline :: Int -> Parser Lexeme
newline = single . Newline

class Parse a where
  parser :: Parser a

lexParse :: Parser a -> Text -> Maybe a
lexParse p t = parseMaybe Language.Parser.lex t >>= parseMaybe p

test :: Pretty a => Parser a -> Text -> IO ()
test p t = case parse Language.Parser.lex "" t of
  Left e -> print e
  Right x -> case parse p "" x of
    Left r -> print r
    Right y -> print $ pretty y

instance Parse Base where
  parser = Int <$ ctr "Int"

instance Parse Constraint where
  parser = choice
    [ Eq  <$ ctr "Eq"  <*> identifier
    , Ord <$ ctr "Ord" <*> identifier
    ]

instance Parse Mono where
  parser = choice
    [ Free <$> identifier
    , brackets Round do
      x <- optional do
        t <- parser
        choice
          [ Product . (t:) <$> some (sep "," *> parser)
          , return t
          ]
      return $ fromMaybe (Product []) x
    , Base <$> parser
    , Data <$> constructor <*> many parser
    ]

instance Parse Signature where
  parser = do
    constraints <- choice
      [ parseList Round parser <* op "=>"
      , (:[]) <$> parser <* op "=>"
      , mempty
      ]
    inputs <- choice
      [ parseList Curly (Named <$> identifier <* op ":" <*> parser) <* op "->"
      , mempty
      ]
    output <- parser
    return Signature { constraints, inputs, output }

instance Parse (Named Signature) where
  parser = Named <$> identifier <* op ":" <*> parser

instance Parse Lit where
  parser = MkInt <$> int

instance Parse (Hole Void) where
  parser = empty

instance Parse (Hole ()) where
  parser = MkHole <$> do
    "_" <- identifier
    return ()

instance Parse (Hole h) => Parse (Hole (Expr l h)) where
  parser = MkHole <$> brackets Curly parser

parenExpr :: Parse (Hole h) => Parser (Expr l h)
parenExpr = brackets Round do
  choice
    [ do
      x <- parser
      choice
        [ Tuple . (x:) <$> some (sep "," *> parser)
        , return x
        ]
    , return Unit
    ]

instance Parse (Hole h) => Parse (Expr l h) where
  parser = choice
    [ parenExpr
    , Ctr <$> constructor <*> option Unit parser
    , mkList <$> parseList Square parser
    , Lit <$> parser
    , Hole <$> parser
    ]

spacedExprUntil :: Parse (Hole h) => Lexeme -> Parser [Expr l h]
spacedExprUntil l = many $ choice
  [ parenExpr
  , mkList <$> parseList Square parser
  , do
    x <- anySingleBut l
    maybe empty return $ parseMaybe parser [x]
  ]

instance Parse Example where
  parser = do
    inputs <- spacedExprUntil (Operator "->")
    output <- optional (op "->" *> parser)
    case (inputs, output) of
      ([out], Nothing ) -> return $ Example [] out
      (_:_  , Just out) -> return $ Example inputs out
      _ -> empty

instance Parse (Named Example) where
  parser = Named <$> identifier <*> do
    Example <$> spacedExprUntil (Operator "=") <* op "=" <*> parser

instance Parse Problem where
  parser = (.value) <$> parser @(Named Problem)

instance Parse (Named Problem) where
  parser = do
    Named name signature <- parser
    bs <- many (statementSep *> parser)
    examples <- forM bs \(Named name' b) -> do
      guard $ name == name'
      return b
    return $ Named name Problem { signature, examples }

instance Parse Void where
  parser = empty
