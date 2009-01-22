module Language.Prolog.Parser where

import Control.Applicative
import Control.Monad
import Text.ParserCombinators.Parsec hiding ((<|>), many)
import qualified Text.ParserCombinators.Parsec as P
import qualified Text.ParserCombinators.Parsec.Token as P
import Text.ParserCombinators.Parsec.Language


clause    = (:-) <$> predicate <*> many predicate
predicate = Pred <$> atom <*> (parens (many1 term) <|> return [])
term      = var <|> Term <$> atom <*> (parens (many1 term) <|> return [])
atom      = identifier
var       = do
  first <- upper
  rest  <- many (alphaNum <|> char '_')
  return (Var (VName first : rest))


-- Lexer
-- ------

whiteSpace= P.whiteSpace lexer
lexeme    = P.lexeme lexer
symbol    = P.symbol lexer
natural   = P.natural lexer
parens    = P.parens lexer
semi      = P.semi lexer
identifier= P.identifier lexer
reserved  = P.reserved lexer
reservedOp= P.reservedOp lexer


lexer :: P.TokenParser ()
lexer  = P.makeTokenParser prologDef

prologStyle :: LanguageDef st
prologStyle= emptyDef
                { commentStart   = "/*"
                , commentEnd     = "*/"
                , commentLine    = "%"
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
            { reservedOpNames = [":-"]
            }

-- Applicative instances for Parsec
-- ---------------------------------
instance Applicative (GenParser c st) where
    pure = return
    (<*>) = ap
instance Alternative (GenParser c st) where
    (<|>) = (P.<|>)
    empty = pzero