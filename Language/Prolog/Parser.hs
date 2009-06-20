module Language.Prolog.Parser where

import Control.Applicative hiding ((<|>))
import qualified Control.Applicative as A
import Control.Monad.Free
import Data.Char (isLower)
import Data.Term.Var (Var)
import qualified Text.ParserCombinators.Parsec.Token as P
import Text.ParserCombinators.Parsec as P hiding ((<|>), many, optional)
import Text.ParserCombinators.Parsec.Applicative
import Text.ParserCombinators.Parsec.Language as P
import Text.ParserCombinators.Parsec.Expr

import qualified Language.Prolog.Syntax as S
import Language.Prolog.Syntax hiding (term, var, ident, int, float, string)

type Comment = String

program  :: GenParser Char st [Clause String]
program   = whiteSpace *> many1 clause <* eof

clause    = ((:-) <$> goal <*> (reservedOp ":-" *> commaSep1 goal <|> return [])) <* dot

query = (reservedOp ":-" *> commaSep1 goal) <* optional dot
goal = (reservedOp "!" >> return Cut <|>
        try infixGoal <|>
        Pred <$> ident <*> (parens (commaSep1 term) <|> return [])
       ) <?> "goal"

infixGoal = do
  t1 <- term
  op <- (((\op x y -> Pred op [x,y]) <$> operator) <|> pure Is <* reserved "is") <?> "operator"
  t2 <- term
  let res = t1 `op` t2
  case res of
    Pred "->" _ -> do {string ";"; t3 <- term; return (Ifte t1 t2 t3)} `mplus` return res
    _           -> return res

term_basic = (var                                  <|>
              simple                               <|>
              lexeme (char '_') >> return wildcard <|>
              S.int    <$> integer                 <|>
              S.float  <$> float                   <|>
              S.string <$> stringLiteral           <|>
              try list1                            <|>
              list2
             ) <?> "term"

simple = aterm <|> atuple where
    aterm  = S.term <$> ident <*> (parens (commaSep1 term) <|> return [])
    atuple = S.tuple <$> parens(commaSep1 term)

var :: (Functor f) => GenParser Char st (Free f Var)
var       = lexeme$ do
  first <- upper
  rest  <- many (alphaNum <|> char '_')
  return (S.var (first : rest))

ident      = (identifier  <|>
             identLiteral <|>
             operator    <|>
             string "{}" <|>
             string ";"
            ) <?> "ident"

list1 = brackets $ do
  terms <- commaSep1 term
  reservedOp "|"
  tail <- term
  return $ cons (foldr1 cons terms) tail

list2 = brackets $ do
  terms <- commaSep term
  return $ foldr cons nil terms

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

lexer :: P.TokenParser st
lexer  = P.makeTokenParser prologDef

prologStyle :: LanguageDef st
prologStyle= emptyDef
                { commentStart   = "/*"
                , commentEnd     = "*/"
                , commentLine    = "%"
                , nestedComments = True
                , identStart     = oneOf ("+-*/\\^`~:.?@#=$&" ++ ['a'..'z'])
                , identLetter	 = alphaNum <|> oneOf "+-*=/\\^`~:?@#$&_"
                , opStart	 = opLetter prologStyle
                , opLetter	 = oneOf "<>!=~|&"
                , reservedOpNames= []
                , reservedNames  = []
                , caseSensitive  = True
                }

prologDef = prologStyle
            { reservedOpNames = [":-","|","!"]
            , reservedNames  = ["is"]
            }

identLiteral = lexeme (between (char '\'')
                               (char '\'' <?> "end of identifier")
                               (many anythingButQuote)
                     ) <?> "quoted identifier"
  where anythingButQuote = try ( char '\'' >> char '\'' >> return '\'' ) <|> noneOf "'"

-- Other
-- -----

-- lowering the precedence of <|> to make it more useful
infixr 0 <|>
(<|>) :: Alternative f => f a -> f a -> f a
(<|>) = (A.<|>)
