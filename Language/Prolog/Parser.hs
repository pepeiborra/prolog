module Language.Prolog.Parser where

import Control.Applicative
import Control.Monad
import Text.ParserCombinators.Parsec hiding ((<|>), many, optional)
import qualified Text.ParserCombinators.Parsec as P
import qualified Text.ParserCombinators.Parsec.Token as P
import Text.ParserCombinators.Parsec.Language

import qualified Language.Prolog.Syntax as S
import Language.Prolog.Syntax hiding (term, var)

type Comment = String
program  :: CharParser () [Either Comment Clause]
program   = whiteSpace *> many1 (Left <$> line_comment <|> Right <$> clause) <* eof

line_comment = lexeme(char '%' *> many (noneOf "\n"))

clause    = (:-) <$> predicate <*> (reservedOp ":-" *> commaSep1 predicate <|> return [])
                                <* optional dot
predicate = reservedOp "!" >> return Cut <|>
            Pred <$> atom <*> (parens (commaSep1 term) <|> return [])
term      = var <|>
            simple <|>
            try list1 <|>
            list2
simple    = S.term <$> atom <*> (parens (commaSep1 term) <|> return [])
var       = lexeme$ do
  first <- upper
  rest  <- many (alphaNum <|> char '_')
  return (S.var (first : rest))
atom      = identifier <|> (show <$> natural)

list1 = brackets $ do
  terms <- commaSep1 term
  reservedOp "|"
  tail <- term
  return $ S.term ":" [foldr1 (\x y -> S.term ":" [x,y]) terms, tail]

list2 = brackets $ do
  terms <- commaSep term
  return $ foldr (\x y -> S.term ":" [x,y]) (S.term "[]" []) terms

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

lexer :: P.TokenParser ()
lexer  = P.makeTokenParser prologDef

prologStyle :: LanguageDef st
prologStyle= emptyDef
                { commentStart   = "/*"
                , commentEnd     = "*/"
                , commentLine    = ""
                , nestedComments = True
                , identStart     = letter
                , identLetter	 = alphaNum <|> oneOf "_'"
--                , opStart	 = opLetter prologStyle
--                , opLetter	 = oneOf ":!#$%&*+./<=>?@\\^|-~"
                , reservedOpNames= []
                , reservedNames  = []
                , caseSensitive  = True
                }

prologDef = prologStyle
            { reservedOpNames = [":-","|","!"]
            }

-- Applicative instances for Parsec
-- ---------------------------------
instance Applicative (GenParser c st) where
    pure = return
    (<*>) = ap
instance Alternative (GenParser c st) where
    (<|>) = (P.<|>)
    empty = pzero