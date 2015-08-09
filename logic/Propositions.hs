{-# LANGUAGE TemplateHaskell #-}
module Propositions where

import qualified Data.Map as M
import qualified Data.Set as S
import Prelude hiding ((.),id)
import Control.Category
import Data.Char
import Data.Maybe
import Data.Void

import Control.Isomorphism.Partial
import Control.Isomorphism.Partial.TH
import Text.Syntax
import qualified Text.Syntax.Parser.Naive
import qualified Text.Syntax.Printer.Naive

-- This could be made more abstract as in the unification-fd package
data Term f v = Symb f [Term f v] | Var v
    deriving (Eq, Show)

type Proposition = Term String String

abbreviations :: M.Map String String
abbreviations = M.fromList
    [ ("and", "∧")
    , ("or", "∨")
    , ("imp", "→")
    , ("True", "⊤")
    , ("False", "⊥")
    ]

infixSymbols :: S.Set String
infixSymbols = S.fromList $ words "∧ ∨ →"

mapVar :: (v1 -> v2) -> Term f v1 -> Term f v2
mapVar vf (Symb f ts) = Symb f $ map (mapVar vf) ts
mapVar vf (Var v) = Var $ vf v

$(defineIsomorphisms ''Term)

letter, digit :: Syntax delta => delta Char
letter  =  subset isLetter <$> token
digit   =  subset isDigit <$> token

parens :: Syntax delta => delta x -> delta x
parens = between (text "(" <* skipSpace) (text ")" <* skipSpace)

expression :: Syntax d => d Proposition
expression = skipSpace *> exp (2::Int)
  where
    exp 0 =
        (symb <$> (pure "⊥" <* (text "⊥" <|> text "False") <* skipSpace) <*> pure []) <|>
        (symb <$> (pure "⊤" <* (text "⊤" <|> text "True")  <* skipSpace) <*> pure []) <|>
        (var  <$> symName) <|>
        (symb <$> symName <*> args) <|>
        parens (exp 2)

    exp 1 = chainl1 (exp 0) (textWithSyn "∧" "&") binarySymb
    exp 2 = chainl1 (exp 1) (textWithSyn "∨" "|") binarySymb

    symName = subset (not . special) <$> many1 (letter <|> digit) <* skipSpace
    args = parens $ sepBy (exp 2) (comma <* skipSpace)

    special s = s `elem` ["⊥", "⊤", "False", "True", "∧", "∨"]


textWithSyn :: Syntax delta => String -> String -> delta String
textWithSyn x y = (text x <|> text y) *> skipSpace *> pure x

-- Helpers to deal with partial-isomorphisms. Tricky puzzle to generate, but as
-- long as the type work out...
binarySymb :: Iso (Term f v, (f, Term f v)) (Term f v)
binarySymb = symb . (id *** twoElementList) . inverse associate .  (commute *** id) . associate

twoElementList :: Iso (a, a) [a]
twoElementList = cons . (id *** (cons . ((id *** nil).unit)))


-- Pretty printer

printTerm :: Proposition -> String
printTerm p = fromMaybe e $ Text.Syntax.Printer.Naive.print expression p
  where e = "Could not pretty-print " ++ show p

parseTerm :: String -> Either String Proposition
parseTerm e = case Text.Syntax.Parser.Naive.parse expression e of
    [] -> Left e1
    [r] -> Right (compat r)
    _  -> Left e2
  where e1 = "Could not parse \"" ++ e ++ "\""
        e2 = "Parsing \"" ++ e ++ "\" is ambiguous"

-- Ground terms are terms with no variables, such as the propositions in the
-- task. We encode that invariant in the type system.
type GroundTerm = Term String Void

parseGroundTerm :: String -> Either String GroundTerm
parseGroundTerm s = fixVar `fmap` parseTerm s

fixVar :: Term a a -> Term a Void
fixVar (Symb f ts) = Symb f $ map fixVar ts
fixVar (Var v) = Symb v []

compat :: Term String a -> Term String a
compat (Symb "and" ts) = Symb "∧" $ map compat ts
compat (Symb "or" ts) = Symb "∨" $ map compat ts
compat (Symb "imp" ts) = Symb "→" $ map compat ts
compat (Symb f ts) = Symb f $ map compat ts
compat (Var v) = Var v
