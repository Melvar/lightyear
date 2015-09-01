-- ------------------------------------------------------------- [ Strings.idr ]
-- Module      : Lightyear.Strings
-- Description : String-related parsers.
--
-- This code is distributed under the BSD 2-clause license.
-- See the file LICENSE in the root directory for its full text.
-- --------------------------------------------------------------------- [ EOH ]
module Lightyear.Strings

import public Data.Vect
import public Data.Fin

import public Control.Monad.Identity

import Lightyear.Core
import Lightyear.Combinators
import Lightyear.Errmsg

%access public

-- -------------------------------------------------------- [ Helper Functions ]
private
nat2int : Nat -> Int
nat2int  Z    = 0
nat2int (S x) = 1 + nat2int x

instance Layout String where
  lineLengths = map (nat2int . Prelude.Strings.length) . lines

-- --------------------------------------------------------- [ A String Parser ]
||| Parsers, specialised to Strings
Parser : Type -> Type
Parser = ParserT Identity String

||| Run a parser against an input string
parse : Parser a -> String -> Either String a
parse f s = let Id r = execParserT f s in case r of
  Success _ x => Right x
  Failure es  => Left $ formatError s es

instance Stream Char String where
  uncons s with (strM s)
    uncons ""             | StrNil       = Nothing
    uncons (strCons x xs) | StrCons x xs = Just (x, xs)

-- ---------------------------------------------------------- [ Reserved Stuff ]

||| A parser that matches some particular character
char : Char -> ParserT m String Char
char c = satisfy (== c) <?> "character '" ++ singleton c ++ "'"

||| A parser that matches a particular string
string : String -> ParserT m String String
string s = pack <$> (traverse char $ unpack s) <?> "string " ++ show s

-- ------------------------------------------------------------------- [ Space ]

||| A parser that skips whitespace
space : ParserT m String ()
space = skip (many $ satisfy isSpace) <?> "whitespace"

||| A simple lexer that strips white space from tokens
lexeme : ParserT m String a -> ParserT m String a
lexeme p = p <* space

-- ------------------------------------------------------------------ [ Tokens ]

||| A parser that matches a specific string, then skips following whitespace
token : String -> ParserT m String ()
token s = lexeme (skip (string s)) <?> "token " ++ show s

||| Parses ',' and trailing whitespace.
comma : ParserT m String ()
comma = token "," <?> "Comma"

||| Parses '=' and trailing whitespace.
equals : ParserT m String ()
equals = token "=" <?> "equals"

||| Parses '.' and trailing whitespace.
dot : ParserT m String ()
dot = token "." <?> "dot"

||| Parses ':' and trailing whitespace.
colon : ParserT m String ()
colon = token ":" <?> "colon"

||| Parses ';' and trailing whitespace.
semi : ParserT m String ()
semi = token ";" <?> "semi colon"

-- -------------------------------------------------- [ Delineated Expressions ]

||| Parses `p` enclosed in parenthesis and returns result of `p`.
parens : ParserT m String a -> ParserT m String a
parens p = between (token "(") (token ")") p

||| Parses `p` enclosed in brackets and returns result of `p`.
brackets : ParserT m String a -> ParserT m String a
brackets p = between (token "[") (token "]") p

||| Parses `p` enclosed in braces and returns the result of `p`.
braces : ParserT m String a -> ParserT m String a
braces p = between (token "{") (token "}") p

||| Parses `p` enclosed in angles and returns the result of `p`.
angles : ParserT m String a -> ParserT m String a
angles p = between (token "<") (token ">") p

||| Parses `p` enclosed in single quotes and returns the result of `p`.
||| Not to be used for charLiterals.
squote : ParserT m String a -> ParserT m String a
squote p = between (char '\'') (char '\'') p

||| Parses `p` enclosed in double quotes and returns the result of `p`.
||| Not to be used for `stringLiterals`.
dquote : ParserT m String a -> ParserT m String a
dquote p = between (char '\"') (char '\"') p

-- --------------------------------------------------- [ Separated Expressions ]
||| Parses /one/ or more occurrences of `p` separated by `comma`.
commaSep1 : ParserT m String a -> ParserT m String (List a)
commaSep1 p = p `sepBy1` comma

||| Parses /zero/ or more occurrences of `p` separated by `comma`.
commaSep : ParserT m String a -> ParserT m String (List a)
commaSep p = p `sepBy` comma

||| Parses /one/ or more occurrences of `p` separated by `semi`.
semiSep1 : ParserT m String a -> ParserT m String (List a)
semiSep1 p = p `sepBy1` semi

||| Parses /zero/ or more occurrences of `p` separated by `semi`.
semiSep : ParserT m String a -> ParserT m String (List a)
semiSep p = p `sepBy` semi

-- ----------------------------------------------------------------- [ Numbers ]

||| Matches a single digit
digit : ParserT m String (Fin 10)
digit = satisfyMaybe fromChar
  where fromChar : Char -> Maybe (Fin 10)
        fromChar '0' = Just FZ
        fromChar '1' = Just (FS (FZ))
        fromChar '2' = Just (FS (FS (FZ)))
        fromChar '3' = Just (FS (FS (FS (FZ))))
        fromChar '4' = Just (FS (FS (FS (FS (FZ)))))
        fromChar '5' = Just (FS (FS (FS (FS (FS (FZ))))))
        fromChar '6' = Just (FS (FS (FS (FS (FS (FS (FZ)))))))
        fromChar '7' = Just (FS (FS (FS (FS (FS (FS (FS (FZ))))))))
        fromChar '8' = Just (FS (FS (FS (FS (FS (FS (FS (FS (FZ)))))))))
        fromChar '9' = Just (FS (FS (FS (FS (FS (FS (FS (FS (FS (FZ))))))))))
        fromChar _   = Nothing

||| Matches an integer literal
integer : Num n => ParserT m String n
integer = do minus <- opt (char '-')
             ds <- some digit
             let theInt = getInteger ds
             case minus of
               Nothing => pure (fromInteger theInt)
               Just _  => pure (fromInteger ((-1) * theInt))
  where getInteger : List (Fin 10) -> Integer
        getInteger = foldl (\a => \b => 10 * a + cast b) 0

-- -------------------------------------------------------- [ Testing Function ]

testParser : Parser a -> String -> IO (Maybe a)
testParser p s = case parse p s of
  Left  e => putStrLn e *> pure Nothing
  Right x => pure (Just x)
-- --------------------------------------------------------------------- [ EOF ]
