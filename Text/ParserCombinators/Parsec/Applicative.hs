module Text.ParserCombinators.Parsec.Applicative where

import Control.Applicative
import Control.Monad
import qualified Text.ParserCombinators.Parsec as P

-- Applicative instances for Parsec
-- ---------------------------------
instance Applicative (P.GenParser c st) where
    pure = return
    (<*>) = ap
instance Alternative (P.GenParser c st) where
    (<|>) = (P.<|>)
    empty = P.pzero