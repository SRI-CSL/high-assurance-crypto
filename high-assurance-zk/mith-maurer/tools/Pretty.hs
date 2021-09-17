{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}

module Pretty where

import Prelude hiding ((<>))
import Text.PrettyPrint
import Text.Ordinal

import Data.Foldable as Foldable
import Data.Int
import Data.Word
import Data.Hashable
import Data.Generics hiding (empty,GT)
import Data.ByteString.Lazy.Char8 hiding (empty)

import Control.Monad
import Control.Monad.Identity
    
class (Monad m) => PP m a where
    pp :: a -> m Doc

semicolon = char ';'

nonemptyParens :: Doc -> Doc
nonemptyParens x = if isEmpty x then empty else parens x

ppid :: PP Identity a => a -> Doc
ppid x = runIdentity (pp x)

pprid :: PP Identity a => a -> String
pprid x = runIdentity (ppr x)

ppr :: PP m a => a -> m String
ppr = liftM show . pp

ppOpt :: Monad m => Maybe a -> (a -> m Doc) -> m Doc
ppOpt Nothing f = return empty
ppOpt (Just x) f = f x

ppMb :: PP m a => Maybe a -> m Doc
ppMb = flip ppOpt pp

abrackets p = char '<' <> p <> char '>'

sepBy :: Foldable t => Doc -> t Doc -> Doc
sepBy sep ps = hsep (punctuate sep $ toList ps)

vbraces x = char '{' $+$ nest 1 x $+$ char '}'

ppOrdinal :: (Show a,Integral a) => a -> Doc
ppOrdinal = text . show . showOrdinal

instance Monad m => PP m Doc where
    pp = return
    
instance Monad m => PP m Ordering where
    pp EQ = return $ text "="
    pp LT = return $ text "<"
    pp GT = return $ text ">"

instance PP m a => PP m (Maybe a) where
    pp Nothing = return empty
    pp (Just x) = pp x

instance Monad m => PP m Integer where
    pp = return . integer

instance Monad m => PP m Int where
    pp = return . int

instance Monad m => PP m Int8 where
    pp = return . text . show
instance Monad m => PP m Int16 where
    pp = return . text . show
instance Monad m => PP m Int32 where
    pp = return . text . show
instance Monad m => PP m Int64 where
    pp = return . text . show

instance Monad m => PP m Word8 where
    pp = return . text . show
instance Monad m => PP m Word16 where
    pp = return . text . show
instance Monad m => PP m Word32 where
    pp = return . text . show
instance Monad m => PP m Word64 where
    pp = return . text . show
instance Monad m => PP m Float where
    pp = return . text . show
instance Monad m => PP m Double where
    pp = return . text . show

instance Monad m => PP m () where
    pp () = return empty

instance Data Doc where
    gunfold _ _ _ = error "gunfold Doc"
    toConstr = error "toConstr Doc"
    dataTypeOf = error "dataTypeOf Doc"

instance Ord Doc where
    compare x y = compare (show x) (show y)

instance Monad m => PP m Bool where
    pp = return . text . show

instance Hashable Doc where
    hashWithSalt i x = hashWithSalt i (show x)