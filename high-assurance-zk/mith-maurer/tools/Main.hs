{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ExtendedDefaultRules #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}

module Main where
    
import System.Console.CmdArgs
import Shelly as Sh
import qualified Data.Text as T
import Data.Semigroup
import System.FilePath
import qualified Data.Set as Set
import Data.Maybe

import ML hiding (ignores)

default (T.Text)

data EcMLArgs = EcMLArgs { infiles :: [String], outfile :: String, qualified :: Maybe String, theories :: [String], flat :: Bool, dirs :: [String], opens :: [String], ignores :: [String] }
    deriving (Show, Data, Typeable)
    
ecmlargs = EcMLArgs
    { infiles = []   &= name "i" &= typ "<file.ec>*"
    , outfile = ""   &= name "o" &= typ "<file.ec>"
    , qualified = Nothing &= name "q" &= typ "qualified EC theory"
    , theories = []  &= name "t" &= typ "<EC declaration>*"
    , flat = False   &= name "f" &= typ "<bool>"
    , dirs = []      &= name "I" &= typ "<directory>*" 
    , opens = []     &= name "O" &= typ "<ML module>*"
    , ignores = []   &= name "r" &= typ "<EC definition>*"
    }
    &= summary "Simple EasyCrypt to OCaml translation tool"
    &= help "ecml -f <file>.ec -t <theory>"

isECPrint :: T.Text -> Bool
isECPrint "* In [theories]:" = True
isECPrint "* In [type declarations]:" = True
isECPrint "* In [operators or predicates]:" = True
isECPrint _ = False

main = do
    args <- cmdArgs ecmlargs
    print args
    let printec = "Print.ec"
    let tempec = "Temp.ec"
    let mkimport m = "require import " <> T.pack m <> "."
    let mkprint t = "print [full] " <> T.pack t <> "."
    let includedirs = concatMap (\d -> ["-I",T.pack d]) (dirs args)
    shelly $ print_stdout False $ do
        Sh.writefile (T.unpack printec) $ T.unlines $
            map mkimport (infiles args) ++ 
            map mkimport (maybeToList $ qualified args) ++ 
            map mkprint (theories args)
        Sh.rm_rf "Print.eco"
        res <- Sh.run "easycrypt" (["compile",printec]++includedirs)
        Sh.writefile tempec $ T.unlines $ filter (not . isECPrint) $ T.lines res
        liftIO $ ecToML (flat args) (opens args) (qualified args) (Set.fromList $ ignores args) (Set.fromList $ map (:[]) $ infiles args) tempec (outfile args)
    