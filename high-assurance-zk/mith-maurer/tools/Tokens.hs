{-# LANGUAGE FlexibleInstances, TypeFamilies, DeriveDataTypeable, ScopedTypeVariables, MultiParamTypeClasses #-}

module Tokens where

import Safe

import Data.Generics
import Text.PrettyPrint

import Data.Digits (digits, unDigits)
import Data.List as List
import Data.List.Split (splitOn)
import Data.Char

import Pretty
import Position
import Location

import Control.Monad
import Prelude hiding ((<>))

data TokenInfo
    = TokenInfo 
        { tSymb :: Token
        , tText :: !String
        , tLoc  :: Position
        }
  deriving (Show,Read,Data,Typeable)

instance Eq TokenInfo where
    x == y = tSymb x == tSymb y
instance Ord TokenInfo where
    compare x y = compare (tSymb x) (tSymb y)

instance Located TokenInfo where
    type LocOf TokenInfo = Position
    loc = tLoc
    updLoc t l = t { tLoc = l }
 
instance Monad m => PP m TokenInfo where
    pp = pp . tSymb
 
data Token 
    = QUALIDENTIFIER [String]
    | QUALNAME [String]
    | QUALOP [String] String
    | QUALPOP [String] String
    | STRING String
    | QUALSTRING [String] String
    | IDENTIFIER String
    | TYARG String
    | FLOAT_LITERAL Double
    | DEC_LITERAL Integer
    | TokenEOF
    | TokenError
    | WITH
    | EXPORT
    | FORALL
    | EXISTS
    | CHAR Char
    | PROJ Integer
    | LE_OP
    | GE_OP
    | TRUE
    | FALSE
    | ARROW
    | LARROW
    | DARROW
    | EQUIV
    | DOTBRACK
    | STARTMOD
    | END
    | THEORY
    | TYPE
    | LET
    | IN
    | OP
    | FUN
    | OF
    | AND_OP
    | OR_OP
    | ANDA_OP
    | CONS_OP
    | CAT_OP
    | UNION_OP
    | INTER_OP
    | DISJ_OP
    | IN_OP
    | ABBREV
    | IF
    | THEN
    | ELSE
    | SUBSET_OP
  deriving (Show,Read,Data,Typeable,Eq,Ord)

instance Monad m => PP m Token where
    pp (QUALIDENTIFIER s) =     return $ sepBy (text ".") (map text s)
    pp (QUALNAME s) = return $ text "%" <> sepBy (text ".") (map text s)
    pp (QUALOP s o) = return $ sepBy (text ".") (map text s) <> text "." <> parens (text o)
    pp (QUALPOP s o) = return $ sepBy (text ".") (map text s) <> text ".[" <> text o <> text "]"
    pp (STRING s) = return $ text (show s)
    pp (QUALSTRING ss s) = return $ sepBy (text ".") (map text ss) <> text "." <> text (show s)
    pp (IDENTIFIER s) =         return $ text s
    pp (TYARG s) =         return $ text "'" <> text s
    pp (FLOAT_LITERAL i) =      return $ text (show i)
    pp (DEC_LITERAL i) =        return $ text (convert_from_base 10 i)
    pp TokenEOF =               return $ text "<EOF>"
    pp TokenError =             return $ text "error <unknown>"
    pp WITH =                 return $ text "with"
    pp EXPORT = return $ text "export"
    pp FORALL =                 return $ text "forall"
    pp EXISTS =                 return $ text "exists"
    pp (CHAR c) =               return $ text [c]
    pp (PROJ i) =               return $ text ".`" <> text (show i)
    pp IN_OP =                  return $ text "\\in"
    pp LE_OP =                  return $ text "<="
    pp GE_OP =                  return $ text ">=" 
    pp AND_OP =                 return $ text "/\\" 
    pp OR_OP =                 return $ text "\\/" 
    pp ANDA_OP =                 return $ text "&&" 
    pp CONS_OP =                 return $ text "::" 
    pp CAT_OP =                 return $ text "++" 
    pp UNION_OP =                 return $ text "`|`" 
    pp INTER_OP =                 return $ text "`&`" 
    pp DISJ_OP =                 return $ text "`\\`" 
    pp TRUE = return $ text "true"
    pp FALSE = return $ text "false"
    pp ARROW = return $ text "->"
    pp LARROW = return $ text "<-"
    pp DARROW = return $ text "=>"
    pp EQUIV = return $ text "<=>"
    pp DOTBRACK = return $ text ".["
    pp STARTMOD = return $ text "`|"
    pp END = return $ text "end"
    pp THEORY = return $ text "theory"
    pp TYPE = return $ text "type"
    pp LET = return $ text "let"
    pp IN = return $ text "in"
    pp OP = return $ text "op"
    pp FUN = return $ text "fun"
    pp OF = return $ text "of"
    pp ABBREV = return $ text "abbrev"
    pp IF = return $ text "if"
    pp THEN = return $ text "then"
    pp ELSE = return $ text "else"
    pp SUBSET_OP = return $ text "\\subset"


convertBase :: Integral a => a -> a -> [a] -> [a]
convertBase from to = digits to . unDigits from

convert_to_base :: Int -> String -> Integer
convert_to_base base input = unDigits (toEnum base) $ convertBase 10 (toEnum base) $ digits 10 $ readInteger input

convert_from_base :: Int -> Integer -> String
convert_from_base base input = concatMap show ds10
    where
    dsBase :: [Integer] = digits (toEnum base) input
    ds10 :: [Integer] = convertBase (toEnum base) 10 dsBase

tokenStr :: TokenInfo -> String
tokenStr (TokenInfo (STRING s) _ _) = s

tokenQStr :: TokenInfo -> ([String],String)
tokenQStr (TokenInfo (QUALSTRING qs s) _ _) = (qs,s)

tokenId :: TokenInfo -> String
tokenId (TokenInfo (IDENTIFIER s) _ _) = s
tokenId t = error $ "tokenId: " ++ show t

tokenTyArg :: TokenInfo -> String
tokenTyArg (TokenInfo (TYARG s) _ _) = s
tokenTyArg t = error $ "tokenTyArg: " ++ show t

tokenQId :: TokenInfo -> ([String],String)
tokenQId (TokenInfo (QUALIDENTIFIER s) _ _) = (init s,last s)

tokenQName :: TokenInfo -> ([String])
tokenQName (TokenInfo (QUALNAME s) _ _) = s

tokenQOp :: TokenInfo -> ([String],String)
tokenQOp (TokenInfo (QUALOP s o) _ _) = (s,o)

tokenQPOp :: TokenInfo -> ([String],String)
tokenQPOp (TokenInfo (QUALPOP s o) _ _) = (s,o)

tokenInteger :: TokenInfo -> Integer
tokenInteger (TokenInfo (DEC_LITERAL f) _ _) = f

tokenFloat :: TokenInfo -> Double
tokenFloat (TokenInfo (FLOAT_LITERAL f) _ _) = f

readInteger :: String -> Integer
readInteger s = readNote ("read Integer " ++ show s) s

readFloat :: String -> Double
readFloat s = readNote ("read Float " ++ show s) s

readQualIden :: String -> [String]
readQualIden = splitOn "."

readQualOp :: String -> Token
readQualOp s = QUALOP (init xs) (noWhite $ tail $ init $ last xs)
    where xs = readQualIden s
    
readQualPOp :: String -> Token
readQualPOp s = QUALPOP (init xs) (noWhite $ tail $ init $ last xs)
    where xs = readQualIden s

noWhite = filter (not . isSpace)
