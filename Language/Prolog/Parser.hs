module Language.Prolog.Parser where

import qualified Control.Applicative as A
import Control.Applicative hiding ((<|>))
import Control.Monad
import Data.Char (isLower)
import Text.ParserCombinators.Parsec hiding ((<|>), many, optional)
import qualified Text.ParserCombinators.Parsec as P
import qualified Text.ParserCombinators.Parsec.Token as P
import Text.ParserCombinators.Parsec.Language
import Text.ParserCombinators.Parsec.Expr

import qualified Language.Prolog.Syntax as S
import Language.Prolog.Syntax hiding (term, var, atom, int, float)

type Comment = String

infixr 0 <|>

(<|>) :: Alternative f => f a -> f a -> f a
(<|>) = (A.<|>)

program  :: CharParser () [Clause]
program   = whiteSpace *> many1 clause <* eof

clause    = (:-) <$> predicate <*> (reservedOp ":-" *> commaSep1 predicate <|> return [])
                                <* optional dot
predicate = (reservedOp "!" >> return Cut <|>
            Pred <$> atom <*> (parens (commaSep1 term) <|> return [])) <?> "predicate"

term_basic = (var <|>
              simple <|>
              lexeme (char '_') >> return wildcard <|>
              S.int <$> integer <|>
              S.float <$> float <|>
              (foldr cons nil . map (S.atom . (:[]))) <$> stringLiteral <|>
              try list1 <|>
              list2)
             <?> "term"

simple = aterm <|> atuple where
    aterm  = S.term <$> atom <*> (parens (commaSep1 term) <|> return [])
    atuple = S.term "" <$> parens(commaSep1 term)

var       = lexeme$ do
  first <- upper
  rest  <- many (alphaNum <|> char '_')
  return (S.var (first : rest))

atom      = (identifier  <|>
             atomLiteral <|>
             operator    <|>
--           string "[]" >> return nil <|>
             string "{}" <|>
--           string "!"  >> return cut <|>
             string ";"
            ) <?> "atom"

list1 = brackets $ do
  terms <- commaSep1 term
  reservedOp "|"
  tail <- term
  return $ S.term "." [foldr1 cons terms, tail]

list2 = brackets $ do
  terms <- commaSep term
  return $ foldr cons nil terms

cons x y =  S.term "." [x,y]
nil      = (S.term "[]" [])

-- Expressions
-- ------------
term    = buildExpressionParser table factor
        <?> "expression"

table   = [[op "*" AssocLeft, op "/" AssocLeft]
          ,[op "+" AssocLeft, op "-" AssocLeft]
          ]
        where
          op s assoc
             = Infix (do{ symbol s; return (\x y -> S.term s [x,y])}) assoc

factor  = (try(parens term) <|> term_basic)
        <?> "simple expression"

-- Lexer
-- ------

whiteSpace= P.whiteSpace lexer
lexeme    = P.lexeme lexer
symbol    = P.symbol lexer
natural   = P.natural lexer
parens    = P.parens lexer
brackets  = P.brackets lexer
dot       = P.dot lexer
semi      = P.semi lexer
identifier= P.identifier lexer
reserved  = P.reserved lexer
reservedOp= P.reservedOp lexer
commaSep  = P.commaSep lexer
commaSep1 = P.commaSep1 lexer
integer   = P.integer lexer
float     = P.float lexer
stringLiteral = P.stringLiteral lexer
operator  = P.operator lexer

lexer :: P.TokenParser ()
lexer  = P.makeTokenParser prologDef

prologStyle :: LanguageDef st
prologStyle= emptyDef
                { commentStart   = "/*"
                , commentEnd     = "*/"
                , commentLine    = "%"
                , nestedComments = True
                , identStart     = do {c <- letter; guard (isLower c); return c}
                , identLetter	 = alphaNum <|> oneOf "_'"
                , opStart	 = opLetter prologStyle
                , opLetter	 = oneOf "+-*/\\^<>=`~:.?@#$&"
                , reservedOpNames= []
                , reservedNames  = []
                , caseSensitive  = True
                }

prologDef = prologStyle
            { reservedOpNames = [":-","|","!"]
            }

atomLiteral = lexeme (between (char '\'')
                                  (char '\'' <?> "end of atom")
                                  (many (identLetter prologStyle))
                     ) <?> "quoted atom"

-- Applicative instances for Parsec
-- ---------------------------------
instance Applicative (GenParser c st) where
    pure = return
    (<*>) = ap
instance Alternative (GenParser c st) where
    (<|>) = (P.<|>)
    empty = pzero