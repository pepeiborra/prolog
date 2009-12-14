module Language.Prolog.Parser where

import Control.Applicative hiding ((<|>))
import qualified Control.Applicative as A
import Control.Monad.Free
import Data.Char (isLower)
import Data.Term.Var (Var)
import qualified Text.ParserCombinators.Parsec.Token as P
import Text.ParserCombinators.Parsec as P hiding ((<|>), many, optional)
import Text.ParserCombinators.Parsec.Language as P
import Text.ParserCombinators.Parsec.Expr

import qualified Language.Prolog.Syntax as S
import Language.Prolog.Syntax hiding (term, var, ident, int, float, string)

type Comment = String

program  :: GenParser Char st [Either [Goal String] (Clause String)]
program   = whiteSpace *> (concat <$> many1 (Left <$$> query <|> Right <$$> clause)) <* eof
  where (<$$>) = fmap . fmap

clause    = do
  g <- goal
  cc_sets <- (reservedOp ":-" *> body) <|> return [[]]
  dot
  return [g :- cc | cc <- cc_sets]

query = reservedOp ":-" *> body <* dot

body = buildExpressionParser table factor  <?> "body"
  where
   table   = [[Infix (comma >> return merge) AssocLeft]
             ,[op ";" (++) AssocLeft, op "|" (++) AssocLeft]
             ]
   op s f assoc = Infix (do{reservedOp s; return f}) assoc
   factor       = (try(parens body) <|> return2 <$> goal) <?> "goal"
   return2      = return . return
   merge cc1 cc2 = [ c1 ++ c2 | c1 <- cc1, c2 <- cc2]

{-
  group_goals <- parens (commaSep1 goal `sepBy1` (reservedOp ";" <|> reservedOp "|")) <|> return []
  dot
  return (map (global_goals ++) group_goals)
-}

goal = (reservedOp "!" >> return Cut <|>
        try infixGoal <|>
        Pred <$> ident <*> (parens (commaSep1 term) <|> return [])
       ) <?> "goal"

infixGoal = do
  t1 <- term
  op <- msum [ reservedOp "="  >> return (:=:)
             , reserved   "is" >> return Is
             , do {op <- operator; return (\x y -> Pred op [x,y])} ]
           <?> "operator"
  t2 <- term
  let res = t1 `op` t2
  case res of
    Pred "->" _ -> do {string ";"; t3 <- term; return (Ifte t1 t2 t3)} `mplus` return res
    _           -> return res

term_basic = (varOrWildcard                        <|>
              simple                               <|>
              S.int    <$> integer                 <|>
              S.float  <$> float                   <|>
              S.string <$> stringLiteral           <|>
              try list1                            <|>
              list2
             ) <?> "term"

simple = aterm <|> atuple where
    aterm  = S.term <$> ident <*> (parens (commaSep1 term) <|> return [])
    atuple = S.tuple <$> parens(commaSep1 term)

varOrWildcard :: GenParser Char st (Free (TermF id) Var)
varOrWildcard = lexeme$ do
  first <- (upper <|> char '_')
  rest  <- many (alphaNum <|> char '_')
  return $ case (first,rest) of
             ('_', []) -> wildcard
             _         -> (S.var (first : rest))

var :: (Functor t) =>GenParser Char st (Free t Var)
var = lexeme$ do
  first <- (upper <|> char '_')
  rest  <- many (alphaNum <|> char '_')
  return $ (S.var (first : rest))

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
comma     = P.comma lexer
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
                , reservedOpNames= ["="]
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
