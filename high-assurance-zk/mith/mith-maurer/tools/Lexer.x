{

{-# LANGUAGE MultiParamTypeClasses #-}

module Lexer where

import Control.Monad.Except
import Control.Monad.State

import Tokens
import Position
import Location
import Error

import Text.PrettyPrint

}

%wrapper "monadUserState"

-- Character classes

$digit           = [0-9]
$underscore      = _
$dot             = \.
$whitespace      = [ \t]
$uppercase       = [A-Z]
$squote          = \'
$lowercase       = [a-z]
$simpleop        = [\\\.\-\,\;\:\!\?\/\^\~\(\)\[\]\{\}\*\&\%\+\<\=\>\|\`]

@newline         = (\n\r|\r\n|\n|\r)
@letter          = ($uppercase|$lowercase)
@nondigit        = ($uppercase|$lowercase|$underscore|$squote)
@decimal         = 0|[1-9]$digit*
@exponent        = (e|E)[\+\-]?@decimal
@identifier      = @nondigit(@nondigit|$digit)*
@tyarg           = \'@identifier
@simplefloat     = @decimal@exponent
@scientificfloat = @decimal\.$digit*@exponent?
@proj            = \.\`@decimal
@qualidentifier  = @identifier($dot@identifier)+
@qualname  = \%@identifier($dot@identifier)*
@slashop = \\@identifier
@op = ($simpleop+|@slashop)
@wop = ($white)*@op($white)*
@qualpop = (@identifier$dot)*\[@wop\]
@qualop = (@identifier$dot)*\(@wop\)
@qualprefix = (@identifier$dot)+

tokens :-


<0>       \(\*                                  { enterNewComment }
<comment> \(\*                                  { embedComment    }
<comment> \*\)                                  { unembedComment  }
<comment> @newline                              { bufferComment }
<comment> .                                     { bufferComment }

<0> lemma                                  { enterIgnore }
<0> axiom                                  { enterIgnore }
<0> module                                 { enterIgnore }
<0> instance                                 { enterIgnore }
<ignore> theory                                 { leaveIgnore THEORY }
<ignore> end                                 { leaveIgnore END }
<ignore> type                                   { leaveIgnore TYPE }
<ignore> op                                     { leaveIgnore OP }
<ignore> abbrev                                 { leaveIgnore ABBREV }
<ignore> @identifier                            { bufferIgnore }
<ignore> @newline                              { bufferIgnore }
<ignore> .                                      { bufferIgnore }

<0>       $white+           ;

-- String literals:   
<0>                     @qualprefix\"           { enterQualStateString }
<0>                     \"                      { enterStateString }
<state_string>          \"                      { leaveStateString }
<state_string>          \\n                     { bufferChar (const '\n') }
<state_string>          \\t                     { bufferChar (const '\t') }
<state_string>          \\r                     { bufferChar (const '\r') }
<state_string>          \\\.                    { bufferChar (!!1) }
<state_string>          .                       { bufferChar (!!0) }

-- Keywords:
<0>                     export                  { lexerTokenInfo EXPORT }
<0>                     forall                  { lexerTokenInfo FORALL }
<0>                     exists                  { lexerTokenInfo EXISTS }
<0>                     theory                  { lexerTokenInfo THEORY }
<0>                     type                    { lexerTokenInfo TYPE }
<0>                     end                     { lexerTokenInfo END }
<0>                     let                     { lexerTokenInfo LET }
<0>                     in                      { lexerTokenInfo IN }
-- <0>                     true                    { lexerTokenInfo TRUE }
-- <0>                     false                   { lexerTokenInfo FALSE }
<0>                     op                      { lexerTokenInfo OP }
<0>                     abbrev                  { lexerTokenInfo ABBREV }
<0>                     fun                     { lexerTokenInfo FUN }
<0>                     with                     { lexerTokenInfo WITH }
<0>                     of                     { lexerTokenInfo OF }
<0>                     if                     { lexerTokenInfo IF }
<0>                     then                     { lexerTokenInfo THEN }
<0>                     else                     { lexerTokenInfo ELSE }

<0>                     @proj                   { lexerTokenInfoFunc (return . PROJ . readInteger . drop 2) }

<0>                     @tyarg                  { lexerTokenInfoFunc (return . TYARG . drop 1) }
<0>                     @qualname               { lexerTokenInfoFunc (return . QUALNAME . readQualIden . drop 1) }
<0>                     @qualidentifier         { lexerTokenInfoFunc (return . QUALIDENTIFIER . readQualIden) }
<0>                     @qualpop              { lexerTokenInfoFunc (return . readQualPOp) }
<0>                     @qualop                 { lexerTokenInfoFunc (return . readQualOp) }
<0>                     @identifier             { lexerTokenInfoFunc (return . IDENTIFIER) }
<0>                     @simplefloat            { lexerTokenInfoFunc (return . FLOAT_LITERAL . readFloat) }
-- <0>                     @scientificfloat        { lexerTokenInfoFunc (return . FLOAT_LITERAL . readFloat) }
<0>                     @decimal                { lexerTokenInfoFunc (return . DEC_LITERAL . convert_to_base 10) }

<0>                     \\in                     { lexerTokenInfo IN_OP }
<0>                     \\subset                     { lexerTokenInfo SUBSET_OP }
<0>                     \->                     { lexerTokenInfo ARROW }
<0>                     \<\-                    { lexerTokenInfo LARROW }
<0>                     \<=                     { lexerTokenInfo LE_OP }
<0>                     >=                      { lexerTokenInfo GE_OP }
<0>                     =>                      { lexerTokenInfo DARROW }
<0>                     \<=>                    { lexerTokenInfo EQUIV }
<0>                     \.\[                    { lexerTokenInfo DOTBRACK }
<0>                     \`\|                    { lexerTokenInfo STARTMOD }
<0>                     \/\\                    { lexerTokenInfo AND_OP }
<0>                     \\\/                    { lexerTokenInfo OR_OP }
<0>                     \:\:                    { lexerTokenInfo CONS_OP }
<0>                     \+\+                    { lexerTokenInfo CAT_OP }
<0>                     \`\|\`                  { lexerTokenInfo UNION_OP }
<0>                     \`\&\`                  { lexerTokenInfo INTER_OP }
<0>                     \`\\\`                  { lexerTokenInfo DISJ_OP }
<0>                     \&\&                  { lexerTokenInfo ANDA_OP }

<0>                     $simpleop               { simpleOp }
<0>                     @newline                { skip }
<0>                     $whitespace             { skip }

<0>                     .                       { lexerTokenInfoFunc handleError     }

{

-- Token Functions -------------------------------------------------------------


lexerTokenInfo :: Token -> AlexInput -> Int -> Alex TokenInfo
lexerTokenInfo t (AlexPn a ln c, _, _, s) l = do
    fn <- alexFilename
    return $ TokenInfo t (take l $ s) (pos fn ln c a)

lexerTokenInfoFunc :: (String -> Alex Token) -> AlexInput -> Int -> Alex TokenInfo
lexerTokenInfoFunc f (AlexPn a ln c, _, _, s) l = do 
    r <- f (take (fromIntegral l) s)
    fn <- alexFilename
    return $ TokenInfo r (take (fromIntegral l) s) (pos fn ln c a)

simpleOp :: AlexInput -> Int -> Alex TokenInfo
simpleOp input len = lexerTokenInfoFunc (return . CHAR . head) input len

handleError :: String -> Alex Token
handleError _ = return TokenError

enterIgnore :: AlexInput -> Int -> Alex TokenInfo
enterIgnore input len = do
    alexSetStartCode ignore
    skip input len

bufferIgnore :: AlexInput -> Int -> Alex TokenInfo
bufferIgnore input@(AlexPn a ln c, _, _, s) len = do
    skip input len

leaveIgnore :: Token -> AlexInput -> Int -> Alex TokenInfo
leaveIgnore tok input len = do
    alexSetStartCode 0
    lexerTokenInfo tok input len

enterNewComment :: AlexInput -> Int -> Alex TokenInfo
enterNewComment input len = do
    modify (\ aus -> aus { commentDepth = 1 })
    alexSetStartCode comment
    skip input len

embedComment :: AlexInput -> Int -> Alex TokenInfo
embedComment input len = do
    modify (\ aus -> aus { commentDepth = commentDepth aus + 1 })
    skip input len

unembedComment :: AlexInput -> Int -> Alex TokenInfo
unembedComment input len = do
    aus <- get
    let cd = commentDepth aus
    put (aus { commentDepth = cd - 1 })
    if (cd == 1)
        then do
            alexSetStartCode 0
            skip input len
        else do
            skip input len
            
bufferComment :: AlexInput -> Int -> Alex TokenInfo
bufferComment input@(AlexPn a ln c, _, _, s) len = do
    skip input len


-- Alex Functions --------------------------------------------------------------

data AlexUserState = AlexUserState 
    { filename     :: !String
    , commentDepth :: Integer
    , stateString  :: ([String],String)
    }

alexFilename :: Alex String
alexFilename = liftM filename get

alexInitUserState :: AlexUserState
alexInitUserState = AlexUserState "" 0 ([],"")

instance MonadState AlexUserState Alex where
    get = alexGetUserState
    put = alexSetUserState

instance MonadError Error Alex where
    throwError e = Alex $ \ s -> Left (show e)
    catchError (Alex un) f = Alex $ \ s -> either (catchMe s) Right (un s)
        where 
        catchMe s x = fmap (split (const s) id) $ runAlex "" $ f $ LexicalError x 

{-# INLINE split #-}
split :: (a -> b) -> (a -> c) -> a -> (b, c)
split f g a = (f a, g a)

alexEOF :: Alex TokenInfo
alexEOF = do 
    (AlexPn a ln c, _, _, _) <- alexGetInput
    fn <- alexFilename
    return $ TokenInfo TokenEOF "<EOF>" (pos fn ln c a)


-- Processing Functions --------------------------------------------------------

positionToAlexPos :: Position -> AlexPosn
positionToAlexPos (Pos fn l c a) = AlexPn a l c

alexSetPos :: AlexPosn -> Alex ()
alexSetPos p = do
    (_,x,y,z) <- alexGetInput
    alexSetInput (p,x,y,z)

runLexerWith ::  String -> String -> AlexPosn -> ([TokenInfo] -> Alex a) -> Either String a
runLexerWith fn str pos parse = runAlex str $ do
    alexSetPos pos
    put (alexInitUserState { filename = fn })
    toks <- getTokens
    parse toks

runLexer :: String -> String -> Either String [TokenInfo]
runLexer fn str = runLexerWith fn str alexStartPos return

injectResult :: Either String a -> Alex a
injectResult (Left err) = throwError (LexicalError err )
injectResult (Right a) = return a

-- | Alex lexer
lexer :: (TokenInfo -> Alex a) -> Alex a
lexer cont = alexMonadScan >>= cont

getTokens :: Alex [TokenInfo]
getTokens = do 
    tok <- alexMonadScan
    case tSymb tok of
        TokenEOF -> return [tok]
        _ -> liftM (tok:) getTokens

flushLexer :: Alex ()
flushLexer = return ()

bufferChar :: (String -> Char) -> AlexInput -> Int -> Alex TokenInfo
bufferChar f input@(AlexPn a ln c, _, _, s) len = do
    modify (\ aus -> aus { stateString = (fst $ stateString aus,snd (stateString aus) ++ [f (take len s)]) } )
    skip input len

enterStateString :: AlexInput -> Int -> Alex TokenInfo
enterStateString input len = do
    modify (\ aus -> aus { stateString = ([],"") } )
    alexSetStartCode state_string
    skip input len

enterQualStateString :: AlexInput -> Int -> Alex TokenInfo
enterQualStateString input@(AlexPn a ln c, _, _, s) len = do
    let qs = readQualIden (take (len-2) s)
    modify (\ aus -> aus { stateString = (qs,"") } )
    alexSetStartCode state_string
    skip input len

leaveStateString :: AlexInput -> Int -> Alex TokenInfo
leaveStateString i n = do
    alexSetStartCode 0
    saveStateString i n
    
saveStateString :: AlexInput -> Int -> Alex TokenInfo
saveStateString input len = do
    aus <- get
    modify (\ aus -> aus { stateString = ([],"") } )
    let (qs,n) = stateString aus
    if null qs
        then lexerTokenInfo (STRING n) input len
        else lexerTokenInfo (QUALSTRING qs n) input len



}