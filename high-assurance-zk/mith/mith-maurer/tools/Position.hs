
{-# LANGUAGE DeriveFoldable, FlexibleInstances, MultiParamTypeClasses #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}

module Position where

import Control.Monad

import Data.Foldable
import Data.Traversable
import Data.Generics (Data, Typeable)
import Data.Hashable

import GHC.Generics (Generic)

import Text.Parsec.Pos
import Text.PrettyPrint

import Pretty
import Prelude hiding ((<>))


-- | Source position
--
data Position
    -- | Normal position line:col - offset
    = Pos    !String  -- filename
             !Int     -- line number
             !Int     -- column number
             !Int     -- offset
    -- | General information
    | UnhelpfulPos String
    deriving (Read, Eq, Ord, Data, Typeable,Generic)

instance Hashable Position

instance Monad m => PP m Position where
    pp (Pos file line col off) = return $ text file <> char ':' <> int line <> char ':' <> int col
    pp (UnhelpfulPos msg) = return $ text msg

instance Show Position where
    show (Pos file line col off) = "file " ++ show file ++ " line " ++ show line ++ " column " ++ show col ++ " offset " ++ show off
    show (UnhelpfulPos s) = s

-- | Create a 'Position'
--
{-# INLINE pos #-}
pos :: String -> Int -> Int -> Int -> Position
pos = Pos

sourcePosToPosition :: SourcePos -> Position
sourcePosToPosition s = Pos (sourceName s) (sourceLine s) (sourceColumn s) (-1)

positionToSourcePos :: Position -> SourcePos
positionToSourcePos (Pos f l c o) = newPos f l c

startPos :: String -> Position
startPos fn = Pos fn 1 1 0

-- | Create default 'Position'
--
defPos :: Position
defPos = UnhelpfulPos "<no location info>"
    
posLine :: Position -> Int
posLine (Pos _ l _ _) = l
posLine (UnhelpfulPos _) = (-1)
    
posFileName :: Position -> String
posFileName (Pos fn _ _ _) = fn
posFileName (UnhelpfulPos str) = "nofile"