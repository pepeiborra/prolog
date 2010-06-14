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
   factor       = ((return2 <$> goal) <|> parens body) <?> "goal"
   return2      = return . return
   merge cc1 cc2 = [ c1 ++ c2 | c1 <- cc1, c2 <- cc2]

{-
  group_goals <- parens (commaSep1 goal `sepBy1` (reservedOp ";" <|> reservedOp "|")) <|> return []
  dot
  return (map (global_goals ++) group_goals)
-}

goal = msum [reservedOp "!" >> return Cut,
             reservedOp "\\+" >> liftM Not goal,
             try infixGoal,
             simpleGoal]
       <?> "goal"
  where

    simpleGoal = Pred <$> atom <*> (parens (commaSep1 term) <|> return [])

atom      = lexeme (many1 (alphaNum <|> oneOf "+-*_/\\^<>=`~:?@#$&") <|>
                    quotedAtom <|>
                    string "{}" <|>
                    string ";"
                   ) <?> "atom"
 where
  quotedAtom = quoted (many anythingButQuote) <?> "quoted identifier"
  anythingButQuote = try ( char '\'' >> char '\'' >> return '\'' ) <|> noneOf "'"

infixGoal = do
  t1 <- term
  do { reservedOp "->";
        gt <- goal;
        do {symbol ";";
            gf <- goal;
            return(Ifte t1 gt gf);
           }
       <|>
       return (Ift t1 gt);
      }
   <|>
   do { op <- msum [ reservedOp "="     >> return (:=:)
                   , symbol     "is"    >> return Is
                   , reservedOp "\\="   >> return ( (Not.) . (:=:))
                   , reservedOp "=\\="  >> return ( (Not.) . (:=:))
                   , reservedOp "\\=="  >> return ( (Not.) . (:=:))
                   , literalReservedOp ">"
                   , literalReservedOp ">="
                   , literalReservedOp "<"
                   , literalReservedOp "=<"
                   , do {p <- operator; return (mkPred p)}
                  ] <?> "operator";
        t2 <- term;
        return (op t1 t2);
      }
     where literalReservedOp op = do {reservedOp op ; return (mkPred op)}
           mkPred p t1 t2 = Pred p [t1,t2]

-- Terms
-- ------------
term = term_compound

term_basic = msum [reservedOp "_" >> return wildcard,
                   var,
                   aterm,
                   atuple,
                   S.int    <$> integer,
                   S.float  <$> float,
                   S.string <$> stringLiteral,
                   try list1,
                   list2
                   ] <?> "term"

aterm  = S.term <$> atom <*> (parens (commaSep1 term) <|> return [])
atuple = S.tuple <$> parens(commaSep1 term)

var :: (Functor t) =>GenParser Char st (Free t Var)
var = lexeme$ do
  first <- (upper <|> char '_')
  rest  <- many (alphaNum <|> char '_')
  return $ (S.var (first : rest))


list1 = brackets $ do
  terms <- commaSep1 term
  reservedOp "|"
  tail <- term
  return $ cons (foldr1 cons terms) tail

list2 = brackets $ do
  terms <- commaSep term
  return $ foldr cons nil terms


term_compound = buildExpressionParser table factor
            <?> "expression"

table   = [[op "*" AssocLeft, op "/" AssocLeft]
          ,[op "+" AssocLeft, op "-" AssocLeft]
          ,[otherop]
          ]
        where
          mkTerm s x y = S.term s [x,y]
          otherop = Infix (do { p <- operator
                              ; return (mkTerm p)})
                          AssocLeft
          op s assoc
             = Infix (do{ reservedOp s; return (mkTerm s)}) assoc

factor  = (term_basic <|> parens term_compound)
        <?> "simple expression"

-- Lexer
-- ------
quoted = lexeme . between (symbol "'") (symbol "'" <?> "end of quotes")

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
                , opLetter	 = oneOf "<>!/\\=~|&:+-*/@$!'"
                , reservedOpNames= ["="]
                , reservedNames  = []
                , caseSensitive  = True
                }

prologDef = prologStyle
            { reservedOpNames = ["_",":-","|","!","\\+","->","-","+","/","*","=", ">", "<", ">=", "=<", "\\=", "=\\=","\\=="]
            , reservedNames  = []
            }

-- Other
-- -----

-- lowering the precedence of <|> to make it more useful
infixr 0 <|>
(<|>) :: Alternative f => f a -> f a -> f a
(<|>) = (A.<|>)
