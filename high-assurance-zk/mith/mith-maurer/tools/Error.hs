{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, DeriveDataTypeable, TypeFamilies, FlexibleContexts, DeriveGeneric #-}

module Error where

import Position
import Tokens
import Pretty
import Location

import Data.Generics hiding (empty,Generic)
import Data.Int
import Data.Word
import Data.Hashable

import GHC.Generics (Generic)

import Control.Monad.Except
import Control.Monad.Writer.Strict (tell,MonadWriter(..))

import Text.PrettyPrint as PP

data Error = LexicalError String
           | ParserError String
    deriving (Show,Typeable,Data,Eq,Ord,Generic)

instance Hashable Error

instance Monad m => PP m Error where
    pp (LexicalError s) = return $ text "Lexical error:" <+> text s
    pp (ParserError s) = return $ text "Parser error:" <+> text s
