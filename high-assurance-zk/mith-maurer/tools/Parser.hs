{-# LANGUAGE FlexibleContexts, RankNTypes, MultiParamTypeClasses, ScopedTypeVariables, ViewPatterns, TupleSections, TypeFamilies #-}

module Parser where

import Position
import Location
import Syntax
import Error
import Pretty hiding (sepBy)
import Tokens
import Lexer

import Text.Parsec
import qualified Text.Parsec as Parsec
import Text.Parsec.Pos
import Text.Parsec.Expr

import Control.Applicative hiding ((<|>),optional,many)
import Control.Monad.IO.Class
import Control.Monad
import Control.Monad.Catch hiding (try)
import Control.Monad.Except
import Control.Monad.Reader (ask)
import Control.Monad.Identity
import Control.Monad.State as State
import Control.Monad.Writer as Writer

import Control.Exception (throwIO)

import System.IO
import System.Exit

import Safe

import Data.List as List
import qualified Data.Foldable as Foldable
import Data.Maybe
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Typeable


instance (Monad m,MonadCatch m) => MonadThrow (ParsecT s u m) where
    throwM = lift . throwM

instance MonadCatch m => MonadCatch (ParsecT s u m) where
    p `catch` h = mkPT $ \s ->
            runParsecT p s `catch` \e ->
                runParsecT (h e) s

data EcM m a = EcM { unEcM :: m (Either Error a) }
  deriving (Typeable)
  
instance MonadTrans EcM where
    lift m = EcM $! liftM (Right) m

instance Monad m => MonadError Error (EcM m) where
    {-# INLINE throwError #-}
    throwError e = EcM $! return $ Left e
    {-# INLINE catchError #-}
    catchError (EcM m) f = EcM $! do
        x <- m
        case x of
            Left err -> unEcM (f err)
            otherwise -> return x

instance MonadIO m => MonadIO (EcM m) where
    {-# INLINE liftIO #-}
    liftIO io = EcM $! liftM (Right ) $ liftIO io

instance Monad m => Functor (EcM m) where
    {-# INLINE fmap #-}
    fmap f (EcM m) = EcM $! do
        e <- m
        case e of
            Left err -> return (Left err)
            Right (x) -> return (Right (f x))

instance Monad m => Applicative (EcM m) where
    {-# INLINE pure #-}
    pure = return
    {-# INLINE (<*>) #-}
    (<*>) = ap

instance Monad m => Monad (EcM m) where
    {-# INLINE return #-}
    return x = EcM $! return $ Right (x)
    {-# INLINE (>>=) #-}
    (EcM m) >>= f = EcM $! do
        ex <- m
        case ex of
            Left err -> return (Left err)
            Right (x) -> do
                ey <- unEcM (f x)
                case ey of
                    Left err -> return (Left err)
                    Right (y) -> return (Right y)  
  
runEcM :: MonadIO m => EcM m a -> m a
runEcM m = do
    e <- unEcM m
    case e of
        Left err -> do
            ppe <- ppr err
            liftIO $! die $! ppe
        Right x -> do
            return x

type EcState = ()
type EcParserT m a = ParsecT [TokenInfo] EcState (EcM m) a

infixr 1 >*< 
(>*<) :: ParsecT s u m a -> ParsecT s u m b -> ParsecT s u m (a,b)
p1 >*< p2 = do
    x <- p1
    y <- p2
    return (x,y)
    
infixr 1 >+< 
(>+<) :: ParsecT s u m a -> ParsecT s u m b -> ParsecT s u m (Either a b)
p1 >+< p2 = liftM Left p1 <||> liftM Right p2

infixr 1 <||>
(<||>) :: ParsecT s u m a -> ParsecT s u m a -> ParsecT s u m a
p1 <||> p2 = try p1 <|> p2

apA :: Applicative f => f a -> (a -> b) -> f b
apA m f = pure f <*> m

apA2 :: Applicative f => f a -> f b -> (a -> b -> c) -> f c
apA2 ma mb f = pure f <*> ma <*> mb

apA3 :: Applicative f => f a -> f b -> f c -> (a -> b -> c -> d) -> f d
apA3 ma mb mc f = pure f <*> ma <*> mb <*> mc

apA4 :: Applicative f => f a -> f b -> f c -> f d -> (a -> b -> c -> d -> e) -> f e
apA4 ma mb mc md f = pure f <*> ma <*> mb <*> mc <*> md

apA5 :: Applicative f => f a -> f b -> f c -> f d -> f e -> (a -> b -> c -> d -> e -> g) -> f g
apA5 ma mb mc md me f = pure f <*> ma <*> mb <*> mc <*> md <*> me

apA6 :: Applicative f => f a -> f b -> f c -> f d -> f e -> f g -> (a -> b -> c -> d -> e -> g -> h) -> f h
apA6 ma mb mc md me mg f = pure f <*> ma <*> mb <*> mc <*> md <*> me <*> mg

apA7 :: Applicative f => f a -> f b -> f c -> f d -> f e -> f g -> f h -> (a -> b -> c -> d -> e -> g -> h -> i) -> f i
apA7 ma mb mc md me mg mh f = pure f <*> ma <*> mb <*> mc <*> md <*> me <*> mg <*> mh

apA8 :: Applicative f => f a -> f b -> f c -> f d -> f e -> f g -> f h -> f i -> (a -> b -> c -> d -> e -> g -> h -> i -> j) -> f j
apA8 ma mb mc md me mg mh mi f = pure f <*> ma <*> mb <*> mc <*> md <*> me <*> mg <*> mh <*> mi

apA9 :: Applicative f => f a -> f b -> f c -> f d -> f e -> f g -> f h -> f i -> f j -> (a -> b -> c -> d -> e -> g -> h -> i -> j -> k) -> f k
apA9 ma mb mc md me mg mh mi mj f = pure f <*> ma <*> mb <*> mc <*> md <*> me <*> mg <*> mh <*> mi <*> mj

ecTok :: (Monad m,MonadCatch m) => Token -> EcParserT m TokenInfo
ecTok t = ecTokPred ((==t) . tSymb)

ecTokPred :: (Monad m,MonadCatch m) => (TokenInfo -> Bool) -> EcParserT m TokenInfo
ecTokPred p = ecTokWith (\x -> if p x then Just x else Nothing)

ecTokWith :: (Monad m,MonadCatch m) => (TokenInfo -> Maybe a) -> EcParserT m a
ecTokWith f = tokenPrim pprid next f
    where
    next p t (s:ss) = positionToSourcePos $ tLoc s
    next p t ts = updatePosString (positionToSourcePos $ tLoc t) (pprid t)
    
ecProj :: (Monad m,MonadCatch m) => EcParserT m Integer
ecProj = ecTokWith $ \tok -> case tSymb tok of
    PROJ i -> Just i
    otherwise -> Nothing

ecChar :: (Monad m,MonadCatch m) => Char -> EcParserT m TokenInfo
ecChar c = ecOneOf [c]

ecDot:: (Monad m,MonadCatch m) => EcParserT m TokenInfo
ecDot = ecChar '.'

ecOneOf :: (Monad m,MonadCatch m) => [Char] -> EcParserT m TokenInfo
ecOneOf str = ecTokPred (p . tSymb)
    where
    p (CHAR c) = List.elem c str
    p _ = False

ecParens :: (Monad m,MonadCatch m) => EcParserT m a -> EcParserT m a
ecParens p = ecChar '(' *> p <* ecChar ')'

ecBraces :: (Monad m,MonadCatch m) => EcParserT m a -> EcParserT m a
ecBraces p = ecChar '{' *> p <* ecChar '}'

ecParens' :: (Monad m,MonadCatch m) => (TokenInfo -> EcParserT m a) -> EcParserT m a
ecParens' p = do
    x1 <- ecChar '('
    x <- p x1
    ecChar ')'
    return x

ecBrackets :: (Monad m,MonadCatch m) => EcParserT m a -> EcParserT m a
ecBrackets p = ecChar '[' *> p <* ecChar ']'

ecBrackets' :: (Monad m,MonadCatch m) => (TokenInfo -> EcParserT m a) -> EcParserT m a
ecBrackets' p = do
    x1 <- ecChar '['
    x <- p x1
    ecChar ']'
    return x

ecABrackets :: (Monad m,MonadCatch m) => EcParserT m a -> EcParserT m a
ecABrackets p = ecChar '<' *> p <* ecChar '>'

ecCBrackets :: (Monad m,MonadCatch m) => EcParserT m a -> EcParserT m a
ecCBrackets p = ecChar '{' *> p <* ecChar '}'

ecCBrackets' :: (Monad m,MonadCatch m) => (TokenInfo -> EcParserT m a) -> EcParserT m a
ecCBrackets' p = do
    x1 <- ecChar '{'
    x <- p x1
    ecChar '}'
    return x

ecFoldl1 :: (Monad m,MonadCatch m) => (a -> b -> EcParserT m a) -> EcParserT m a -> EcParserT m b -> EcParserT m a
ecFoldl1 f ma mb = do
    x <- ma
    ys <- many1 mb
    Foldable.foldlM f x ys
    
ecFoldl :: (Monad m,MonadCatch m) => (a -> b -> EcParserT m a) -> EcParserT m a -> EcParserT m b -> EcParserT m a
ecFoldl f ma mb = do
    x <- ma
    ys <- many mb
    Foldable.foldlM f x ys
    
ecFoldr :: (Monad m,MonadCatch m) => (a -> b -> EcParserT m b) -> EcParserT m a -> EcParserT m b -> EcParserT m b
ecFoldr f ma mb = do
    ys <- many ma
    x <- mb
    Foldable.foldrM f x ys

ecMany :: EcParserT m a -> EcParserT m [a]
ecMany p = ecMaybeCont p $ \mb -> case mb of
    Nothing -> return []
    Just x -> do
        xs <- ecMany p
        return (x:xs)

ecMany1 :: EcParserT m a -> EcParserT m [a]
ecMany1 p = do
    x <- p
    xs <- ecMany p
    return (x:xs)

ecSepBy :: EcParserT m a -> EcParserT m sep -> EcParserT m [a]
ecSepBy p sep = ecSepBy1 p sep <||> return []

ecSepBy1 :: EcParserT m a -> EcParserT m sep -> EcParserT m [a]
ecSepBy1 p sep = do
    x <- p
    xs <- ecMany (sep >> p)
    return (x:xs)

ecEmpty :: EcParserT m ()
ecEmpty = return ()

maybeEc :: Maybe a -> EcParserT m a
maybeEc (Just a) = return a
maybeEc Nothing = fail "maybeEc"

ecMaybe :: EcParserT m a -> EcParserT m (Maybe a)
ecMaybe p = (liftM Just p) <||> return Nothing

ecMaybeCont :: EcParserT m a -> (Maybe a -> EcParserT m b) -> EcParserT m b
ecMaybeCont p cont = (p >>= cont . Just) <||> cont Nothing
                
ecMaybeContPair :: EcParserT m a -> EcParserT m b -> EcParserT m (Maybe a,b)
ecMaybeContPair p cont = ecMaybeCont p (\mb -> liftM (mb,) cont)

-- * Grammar

-- ** Literals

ecIntLiteral :: (Monad m,MonadCatch m) => EcParserT m (Literal Position)
ecIntLiteral = liftM (\x1 -> IntLit (loc x1) (tokenInteger x1)) (ecTokPred p) <?> "int literal"
    where
    p (TokenInfo (DEC_LITERAL _) _ _) = True
    p _ = False

ecFloatLiteral :: (Monad m,MonadCatch m) => EcParserT m (Literal Position)
ecFloatLiteral = liftM (\x1 -> FloatLit (loc x1) (tokenFloat x1)) (ecTokPred p) <?> "float literal"
    where
    p (TokenInfo (FLOAT_LITERAL _) _ _) = True
    p _ = False
    
ecBoolLiteral :: (Monad m,MonadCatch m) => EcParserT m (Literal Position)
ecBoolLiteral = apA (ecTok TRUE) (\x1 -> BoolLit (loc x1) True)
            <|> apA (ecTok FALSE) (\x1 -> BoolLit (loc x1) False)

ecLiteral :: (Monad m,MonadCatch m) => EcParserT m (Literal Position)
ecLiteral = ecIntLiteral <|> ecFloatLiteral <|> ecBoolLiteral

-- ** Identifiers

ecQualIdentifier :: (Monad m,MonadCatch m) => EcParserT m TokenInfo
ecQualIdentifier = ecTokPred (p . tSymb) <?> "qid"
    where
    p (QUALIDENTIFIER s) = True
    p _ = False

ecQualName :: (Monad m,MonadCatch m) => EcParserT m TokenInfo
ecQualName = ecTokPred (p . tSymb) <?> "qid"
    where
    p (QUALNAME s) = True
    p _ = False
    
ecQualOp :: (Monad m,MonadCatch m) => EcParserT m TokenInfo
ecQualOp = ecTokPred (p . tSymb) <?> "qparens"
    where
    p (QUALOP s o) = True
    p _ = False

ecOp :: (Monad m,MonadCatch m) => EcParserT m TokenInfo
ecOp = ecTokPred (p . tSymb) <?> "op"
    where
    p (QUALOP [] o) = True
    p _ = False
    
ecQualOp' :: (Monad m,MonadCatch m) => (Position -> Op Identifier Position) -> EcParserT m TokenInfo
ecQualOp' op = ecTokPred (p . tSymb) <?> "qparens"
    where
    p (QUALOP s o) = o == showOp (op noloc)
    p _ = False
    
ecPOp :: (Monad m,MonadCatch m) => EcParserT m TokenInfo
ecPOp = ecTokPred (p . tSymb) <?> "pop"
    where
    p (QUALPOP [] o) = True
    p _ = False
    
ecQualPOp :: (Monad m,MonadCatch m) => EcParserT m TokenInfo
ecQualPOp = ecTokPred (p . tSymb) <?> "qparens"
    where
    p (QUALPOP s o) = True
    p _ = False
    
ecQualPOp' :: (Monad m,MonadCatch m) => (Position -> PreOp Identifier Position) -> EcParserT m TokenInfo
ecQualPOp' op = ecTokPred (p . tSymb) <?> "qparens"
    where
    p (QUALPOP s o) = o == showPreOp (op noloc)
    p _ = False

ecIdentifier :: (Monad m,MonadCatch m) => EcParserT m TokenInfo
ecIdentifier = ecTokPred (p . tSymb) <?> "id"
    where
    p (IDENTIFIER s) = True
    p _ = False
    
ecString :: (Monad m,MonadCatch m) => EcParserT m TokenInfo
ecString = ecTokPred (p . tSymb) <?> "id"
    where
    p (STRING s) = True
    p _ = False
    
ecQualString :: (Monad m,MonadCatch m) => EcParserT m TokenInfo
ecQualString = ecTokPred (p . tSymb) <?> "id"
    where
    p (QUALSTRING qs s) = True
    p _ = False
    
ecTyArg :: (Monad m,MonadCatch m) => EcParserT m TokenInfo
ecTyArg = ecTokPred (p . tSymb) <?> "tyarg"
    where
    p (TYARG s) = True
    p _ = False

ecEOF :: (Monad m,MonadCatch m) => EcParserT m ()
ecEOF = ecTokPred (p . tSymb) >> return ()
    where
    p TokenEOF = True
    p _ = False

-- ** Variables

ecTheoryName :: (MonadIO m,MonadCatch m) => EcParserT m (TheoryName Identifier Position)
ecTheoryName = apA ecIdentifier (\x -> TheoryName (loc x) (tokenId x)) <?> "theory name"

ecTypeName :: (MonadIO m,MonadCatch m) => EcParserT m (TypeName Identifier Position)
ecTypeName = apA ecIdentifier (\x -> TypeName (loc x) (tokenId x)) <?> "type name"

ecTypeArg :: (MonadIO m,MonadCatch m) => EcParserT m (TypeArg Identifier Position)
ecTypeArg = do
    tok <- ecTyArg
    let n = tokenTyArg tok
    return $ TypeArg (loc tok) (n)

ecVarName :: (MonadIO m,MonadCatch m) => EcParserT m (VarName Identifier Position)
ecVarName = apA ecIdentifier (\x -> VarName (loc x) (tokenId x)) <?> "var name"

ecQualTheoryName :: (MonadIO m,MonadCatch m) => EcParserT m (QualifiedTheoryName Identifier Position)
ecQualTheoryName = (apA ecQualIdentifier mk1 <||> apA ecTheoryName mk2) <?> "qual var name"
    where
    mk1 x = let (qs,n) = tokenQId x in Qualified (loc x) qs (TheoryName (loc x) n)
    mk2 x = Qualified (loc x) [] x

ecQualVarName :: (MonadIO m,MonadCatch m) => EcParserT m (QualifiedVarName Identifier Position)
ecQualVarName = (apA ecQualIdentifier mk1 <||> apA ecVarName mk2) <?> "qual var name"
    where
    mk1 x = let (qs,n) = tokenQId x in Qualified (loc x) qs (VarName (loc x) n)
    mk2 x = Qualified (loc x) [] x

ecQualTypeName :: (MonadIO m,MonadCatch m) => EcParserT m (QualifiedTypeName Identifier Position)
ecQualTypeName = (apA ecQualIdentifier mk1 <||> apA ecTypeName mk2) <?> "qual type name"
    where
    mk1 x = let (qs,n) = tokenQId x in Qualified (loc x) qs (TypeName (loc x) n)
    mk2 x = Qualified (loc x) [] x

ecOperatorName :: (MonadIO m,MonadCatch m) => EcParserT m (OperatorName Identifier Position)
ecOperatorName = (apA ecIdentifier (\x -> OperatorName (loc x) (tokenId x)) <?> "operator name")
            <||> (apA ecString (\x -> InfixOperatorName (loc x) (tokenStr x)) <?> "infix operator name")
            <||> (apA ecBinOp (\x -> InfixBinOp (loc x) x) <?> "infix binop")
            <||> (apA ecPreOp (\x -> InfixPreOp (loc x) x) <?> "infix pop")

ecBinOp :: (MonadIO m,MonadCatch m) => EcParserT m (Op Identifier Position)
ecBinOp = do
    tok <- ecOp
    maybeEc $ parseOp (snd $ tokenQOp tok)   
    
ecPreOp :: (MonadIO m,MonadCatch m) => EcParserT m (PreOp Identifier Position)
ecPreOp = do
    tok <- ecPOp
    maybeEc $ parsePreOp (snd $ tokenQPOp tok)
    
ecQBinOp :: (MonadIO m,MonadCatch m) => EcParserT m (QualifiedOperatorName Identifier Position)
ecQBinOp = do
    tok <- ecQualOp
    let (qn,n) = tokenQOp tok
    op <- maybeEc $ parseOp n
    return $ Qualified (loc tok) qn $ InfixBinOp (loc tok) op
    
ecQPreOp :: (MonadIO m,MonadCatch m) => EcParserT m (QualifiedOperatorName Identifier Position)
ecQPreOp = do
    tok <- ecQualPOp
    let (qn,n) = tokenQPOp tok
    op <- maybeEc $ parsePreOp n
    return $ Qualified (loc tok) qn $ InfixPreOp (loc tok) op

ecQualOperatorName :: (MonadIO m,MonadCatch m) => EcParserT m (QualifiedOperatorName Identifier Position)
ecQualOperatorName = (apA ecQualIdentifier mk1
                 <||> apA ecQualString mk2
                 <||> apA ecOperatorName mk3
                 <||> ecQBinOp
                 <||> ecQPreOp)
                 <?> "qual operator name"
    where
    mk1 x = let (qs,n) = tokenQId x in Qualified (loc x) qs (OperatorName (loc x) n)
    mk2 x = let (qs,n) = tokenQStr x in Qualified (loc x) qs (InfixOperatorName (loc x) n)
    mk3 x = Qualified (loc x) [] x

-- ** Program and variable declarations

ecProgram :: (MonadIO m,MonadCatch m) => EcParserT m (Program Identifier Position)
ecProgram = many ecDeclaration <* ecEOF <?> "program"

ecDeclaration :: (MonadIO m,MonadCatch m) => EcParserT m (Declaration Identifier Position)
ecDeclaration = (apA ecOperatorDeclaration (\x -> OperatorDec (loc x) x) <?> "operator declaration")
            <|> (apA ecAbbrevDeclaration (\x -> AbbrevDec (loc x) x) <?> "abbrev declaration")
            <|> (apA ecTheoryDeclaration (\x -> TheoryDec (loc x) x) <?> "theory declaration")
            <|> (apA ecTypeDeclaration (\x -> TypeDec (loc x) x) <?> "type declaration")
            <|> (apA ecExportDeclaration (\x -> ExportDec (loc x) x) <?> "export declaration")

ecExportDeclaration :: (MonadIO m,MonadCatch m) => EcParserT m (ExportDeclaration Identifier Position)
ecExportDeclaration = do
    tok1 <- ecTok EXPORT
    tn <- ecQualTheoryName
    ecDot
    return $ ExportDeclaration (loc tn) tn

ecTheoryDeclaration :: (MonadIO m,MonadCatch m) => EcParserT m (TheoryDeclaration Identifier Position)
ecTheoryDeclaration = do
    tok1 <- ecTok THEORY
    tn@(TheoryName _ n) <- ecTheoryName
    ecDot
    decs <- many ecDeclaration
    tok2 <- ecTok END
    (TheoryName _ n') <- ecTheoryName
    unless (n==n') $ throwError $ ParserError $ show (loc tok1) ++" "++ show (loc tok2) ++ ": unexpected theory closing " ++ show n ++" "++ show n'
    ecDot
    return $ TheoryDeclaration (loc tn) tn decs
    
ecTypeHeaderDeclaration :: (MonadIO m,MonadCatch m) => EcParserT m (Position,TypeArgs Identifier Position,TypeName Identifier Position)
ecTypeHeaderDeclaration = apA3 (ecTok TYPE) ecTypeArgs ecTypeName (\x x1 x2 -> (loc x,x1,x2))
                     <||> apA2 (ecTok TYPE) ecTypeName (\x x1 -> (loc x,[],x1))

ecTyConDecl :: (MonadIO m,MonadCatch m) => EcParserT m (OperatorName Identifier Position,[Type Identifier Position])
ecTyConDecl = do
    cn <- ecOperatorName
    mb <- ecMaybe $ ecTok OF *> ecSepBy1 ecType (ecChar '&')
    return (cn,maybe [] id mb)

ecTypeBodyDeclaration :: (MonadIO m,MonadCatch m) => EcParserT m (TypeBodyDeclaration Identifier Position)
ecTypeBodyDeclaration = ecBrackets (apA2 ecPosition (ecSepBy1 ecTyConDecl (ecChar '|')) (\p cs -> TyDataDeclaration p cs))
                   <||> apA ecType (\t -> TySynDeclaration (loc t) t)
    
ecTypeDeclaration :: (MonadIO m,MonadCatch m) => EcParserT m (TypeDeclaration Identifier Position)
ecTypeDeclaration = (do
    (p,args,n) <- ecTypeHeaderDeclaration
    body <- ecMaybe (ecChar '=' *> ecTypeBodyDeclaration)
    ecDot
    return $ TypeDeclaration p args n body) <?> "type declaration"

ecTypeArgs :: (MonadIO m,MonadCatch m) => EcParserT m (TypeArgs Identifier Position)
ecTypeArgs = (ecParens (sepBy1 ecTypeArg (ecChar ',')))
         <||> (liftM (:[]) ecTypeArg)
         
ecOperatorTypeArgs :: (MonadIO m,MonadCatch m) => EcParserT m (TypeArgs Identifier Position)
ecOperatorTypeArgs = ecBrackets (sepBy1 ecTypeArg (ecChar ',' >+< ecEmpty))

ecTypes :: (MonadIO m,MonadCatch m) => EcParserT m [Type Identifier Position]
ecTypes = (ecParens (sepBy1 ecType (ecChar ',')))

ecType :: (MonadIO m,MonadCatch m) => EcParserT m (Type Identifier Position)
ecType = ecFunType 

ecFunType :: (MonadIO m,MonadCatch m) => EcParserT m (Type Identifier Position)
ecFunType = do
    ts <- (ecFoldl (\x (_,y) -> return $ x ++ [y]) (liftM (:[]) ecProdType) (ecTok ARROW >*< ecProdType)) <?> "fun type"
    return $ go ts
  where
    go [x] = x
    go (x:xs) = FunType (loc x) x (go xs)

ecProdType :: (MonadIO m,MonadCatch m) => EcParserT m (Type Identifier Position)
ecProdType = (liftM mk $ ecFoldl (\xs (_,y) -> return $ xs++[y]) (liftM (:[]) ecAppType) (ecChar '*' >*< ecAppType)) <?> "prod type"
    where mk xs = prodType (loc $ head xs) xs

ecAppType :: (MonadIO m,MonadCatch m) => EcParserT m (Type Identifier Position)
ecAppType = (ecFoldl mksimple ecBaseType ecQualTypeName) 
  where
  mksimple x1 x2 = return $ AppType (loc x1) [x1] x2       
    
ecBaseType :: (MonadIO m,MonadCatch m) => EcParserT m (Type Identifier Position)
ecBaseType = ((apA ecTypeArg (\x -> VarType (loc x) x) <?> "var type"))
        <||> ((ecParens ecType))
        <||> (apA3 ecPosition ecTypes ecQualTypeName (\p x1 x2 -> AppType p x1 x2))
        <||> apA ecQualTypeName (\x -> AppType (loc x) [] x)

ecOperatorDeclaration :: (MonadIO m,MonadCatch m) => EcParserT m (OperatorDeclaration Identifier Position)
ecOperatorDeclaration = apA6 (ecTok OP) ecOperatorName (ecMaybe ecOperatorTypeArgs) ecOperatorSignature ecOperatorBody ecDot (\x1 x2 tys x3 x4 x5 -> OperatorDeclaration (loc x1) x2 tys x3 x4) <?> "operator declaration"

ecAbbrevDeclaration :: (MonadIO m,MonadCatch m) => EcParserT m (AbbrevDeclaration Identifier Position)
ecAbbrevDeclaration = apA6 (ecTok ABBREV) ecOperatorName (ecMaybe ecOperatorTypeArgs) ecOperatorSignature ecOperatorBody ecDot (\x1 x2 tys x3 x4 x5 -> AbbrevDeclaration (loc x1) x2 tys x3 x4) <?> "abbrev declaration"

ecLhsVarName :: (MonadIO m,MonadCatch m) => EcParserT m (Lhs Identifier Position)
ecLhsVarName = do
    v <- ecQualVarName
    return $ VarLhs (loc v) $ v

ecMaybeType :: (MonadIO m,MonadCatch m) => EcParserT m (Maybe (Type Identifier Position))
ecMaybeType = ecMaybeCont (ecChar ':') $ \mb -> case mb of
    Nothing -> return Nothing
    Just _ -> do
        ty <- ecType
        return $ Just ty

ecOperatorArg :: (MonadIO m,MonadCatch m) => EcParserT m (OperatorArg Identifier Position)
ecOperatorArg = ecParens ecOperatorArg
           <|> (apA3 ecPosition (ecMany1 ecLhsVarName) ecMaybeType (\p x1 x2 -> OperatorArg p x1 x2)) <?> "operator arg"

ecOperatorArgs :: (MonadIO m,MonadCatch m) => EcParserT m (OperatorArgs Identifier Position)
ecOperatorArgs = ecMany ecOperatorArg

ecOperatorSignature :: (MonadIO m,MonadCatch m) => EcParserT m (OperatorSignature Identifier Position)
ecOperatorSignature = do
    p <- ecPosition
    args <- ecOperatorArgs 
    ecMaybeCont (ecChar ':') $ \mb -> case mb of
        Nothing -> return $ OperatorSignature p args Nothing
        Just tok -> do
            ty <- ecType
            return $ OperatorSignature p args (Just ty)

ecOperatorBody :: (MonadIO m,MonadCatch m) => EcParserT m (Maybe (Expression Identifier Position))
ecOperatorBody = ecMaybeCont (ecChar '=') $ \mb -> case mb of
    Nothing -> return Nothing
    Just _ -> liftM Just ecExpression

ecExpression :: (MonadIO m,MonadCatch m) => EcParserT m (Expression Identifier Position)
ecExpression = ecWithExpr

ecWithExpr :: (MonadIO m,MonadCatch m) => EcParserT m (Expression Identifier Position)
ecWithExpr = (apA2 ecPosition (many1 ecWithPat) (\p xs -> WithExpr p xs) <?> "with expr")
        <||> ecBinExpr

ecAppExpr :: (MonadIO m,MonadCatch m) => EcParserT m (Expression Identifier Position)
ecAppExpr = (apA2 ecQualOperatorName (ecMany1 ecMapExpr) mk <?> "app expr")
       <||> ecMapExpr
    where mk x1 x2 = AppExpr (loc x1) x1 x2

ecMapExpr :: (MonadIO m,MonadCatch m) => EcParserT m (Expression Identifier Position)
ecMapExpr = ecFoldl mk ecModExpr ecGetSetModExpr <?> "map expr"
    where
    mk x1 (Left x2) = return $ GetExpr (loc x1) x1 x2
    mk x1 (Right (x2,x3)) = return $ SetExpr (loc x1) x1 x2 x3
    ecGetSetExpr = do
        e1 <- ecExpression
        ecMaybeCont (ecTok LARROW *> ecExpression) $ \mb -> case mb of
            Nothing -> return $ Left e1
            Just e2 -> return $ Right (e1,e2)
    ecGetSetModExpr = (ecTok DOTBRACK *> ecGetSetExpr <* ecChar ']')

ecModExpr :: (MonadIO m,MonadCatch m) => EcParserT m (Expression Identifier Position)
ecModExpr = apA3 (ecTok STARTMOD) ecExpression (ecChar '|') (\x1 x2 x3 -> ModExpr (loc x1) x2)
       <||> ecProjExpr

ecProjExpr :: (MonadIO m,MonadCatch m) => EcParserT m (Expression Identifier Position)
ecProjExpr = ecFoldl mk ecBaseExpr ecProj <?> "proj expr"
    where mk x1 x2 = return $ ProjExpr (loc x1) x1 x2

--ecBinExpr :: (MonadIO m,MonadCatch m) => EcParserT m (Expression Identifier Position)
--ecBinExpr = ecFoldl mk ecAppExpr (ecQBinOp >*< ecAppExpr) <?> "bin expr"
--    where mk x1 (o,x2) = return $ BinOpExpr (loc x1) x1 o x2

applyQualName :: (MonadIO m,MonadCatch m) => [String] -> (Expression Identifier Position) -> EcParserT m (Expression Identifier Position) 
applyQualName qn (AppExpr l1 (Qualified l [] n) es) = return $ AppExpr l1 (Qualified l qn n) es
applyQualName qn (GetExpr l1 xs i) = return $ AppExpr l1 (Qualified l1 qn $ InfixOperatorName l1 "_.[_]") [xs,i]
applyQualName qn (SetExpr l1 xs i x) = return $ AppExpr l1 (Qualified l1 qn $ InfixOperatorName l1 "_.[_<-_]") [xs,i,x]
applyQualName qn (BinOpExpr l1 e1 (Qualified l [] op) e2) = return $ AppExpr l1 (Qualified l1 qn $ OperatorName l1 (opName op)) [e1,e2]
--applyQualName qn (BinOpExpr l1 e1 (OpIn l2) e2) = return $ AppExpr l1 (Qualified l1 qn $ OperatorName l1 "mem") [e2,e1]
--applyQualName qn (BinOpExpr l1 e1 (OpSubset l2) e2) = return $ AppExpr l1 (Qualified l1 qn $ OperatorName l1 "subset") [e2,e1]
--applyQualName qn e@(BinOpExpr l1 e1 (OpEq l2) e2) = return $ AppExpr l1 (Qualified l1 qn $ OperatorName l1 "(=)") [e1,e2]
--applyQualName qn e@(BinOpExpr l1 e1 (OpLe l2) e2) = return $ AppExpr l1 (Qualified l1 qn $ OperatorName l1 "(<=)") [e1,e2]
--applyQualName qn e@(BinOpExpr l1 e1 (OpLt l2) e2) = return $ AppExpr l1 (Qualified l1 qn $ OperatorName l1 "(<)") [e1,e2]
applyQualName qn (NilExpr l1) = return $ AppExpr l1 (Qualified l1 qn $ OperatorName l1 "[]") []
applyQualName qn e = throwError $ ParserError $ "unexpected dollar qualified expression " ++ show qn ++ " " ++ show e 
    
ecBaseExpr :: (MonadIO m,MonadCatch m) => EcParserT m (Expression Identifier Position)
ecBaseExpr = (ecDollarExpr <?> "dollar expr")
          <||> (apA6 (ecTok LET) ecLhs (ecChar '=') ecExpression (ecTok IN) ecExpression (\x1 x2 x3 x4 x5 x6 -> LetExpr (loc x1) x2 x4 x6) <?> "let expr")
          <||> (apA4 (ecTok FUN) ecOperatorArgs (ecTok DARROW) ecExpression (\x1 x2 x3 x4 -> FunExpr (loc x1) x2 x4) <?> "fun expr")
          <||> (apA2 ecPosition (ecParens (sepBy ecExpression (ecChar ','))) (\x1 x2 -> prodExpr x1 x2) <?> "prod expr")
          <||> (apA ecVarName (\x -> VarExpr (loc x) x) <?> "var expr")
          <||> (apA ecQualOperatorName (\x -> AppExpr (loc x) x []) <?> "single app expr")
          <||> (apA ecLiteral (\x1 -> LitExpr (loc x1) x1) <?> "lit expr")
          <||> (apA2 (ecChar '[') (ecChar ']') (\x1 x2 -> NilExpr (loc x1)) <?> "nil expr")
          <||> (apA6 (ecTok IF) ecExpression (ecTok THEN) ecExpression (ecTok ELSE) ecExpression (\x1 x2 x3 x4 x5 x6 -> IfThenElseExpr (loc x1) x2 x4 x6) <?> "ifthenelse expr")
          <||> (apA4 (ecTok FORALL) ecOperatorArgs (ecChar ',') ecExpression (\x1 x2 x3 x4 -> ForallExpr (loc x1) x2 x4) <?> "forall expr")
          
ecWithPat :: (MonadIO m,MonadCatch m) => EcParserT m (WithPattern Identifier Position)
ecWithPat = (do
    tok <- ecTok WITH
    lhs <- flip sepBy1 (ecChar ',') $ do
        vn <- ecVarName
        ecChar '='
        lh <- ecLhs
        return (vn,lh)
    ecTok DARROW
    rhs <- ecBinExpr
    return $ WithPattern (loc tok) lhs rhs) <?> "with pat"

ecDollarExpr :: (MonadIO m,MonadCatch m) => EcParserT m (Expression Identifier Position)    
ecDollarExpr = do
    x1 <- ecParens ecExpression
    ecMaybeCont ecQualName $ \mb -> case mb of
        Nothing -> return x1
        Just qn -> applyQualName (tokenQName qn) x1  

ecLhs :: (MonadIO m,MonadCatch m) => EcParserT m (Lhs Identifier Position)
ecLhs = ecAppLhs

ecAppLhs :: (MonadIO m,MonadCatch m) => EcParserT m (Lhs Identifier Position)
ecAppLhs = (apA2 ecQualOperatorName (ecMany ecBinLhs) mk <?> "app lhs")
       <||> ecBinLhs
    where mk x1 x2 = AppLhs (loc x1) x1 x2

ecBinLhs :: (MonadIO m,MonadCatch m) => EcParserT m (Lhs Identifier Position)
ecBinLhs = ecFoldl mk ecBaseLhs (ecBinOpLhs >*< ecBaseLhs) <?> "bin lhs"
    where mk x1 (o,x2) = return $ BinOpLhs (loc x1) x1 o x2

ecBaseLhs :: (MonadIO m,MonadCatch m) => EcParserT m (Lhs Identifier Position)
ecBaseLhs = apA ecQualVarName (\x -> VarLhs (loc x) x)
   <||> apA2 ecPosition (ecParens (sepBy ecLhs (ecChar ','))) (\p x -> prodLhs p x)
   <||> apA2 (ecChar '[') (ecChar ']') (\x1 x2 -> NilLhs (loc x1))

--ecQBinOp :: (MonadIO m,MonadCatch m) => EcParserT m (QualifiedOp Identifier Position)
--ecQBinOp = apA ecBinOp (\x1 -> Qualified (loc x1) [] x1)
--     <||> apA3 ecQualParens ecBinOp (ecChar ')') (\x1 x2 x3 -> Qualified (loc x1) (tokenQParens x1) x2)

--ecBinOp :: (MonadIO m,MonadCatch m) => EcParserT m (Op Identifier Position)
--ecBinOp = apA (ecTok GE_OP) (\x1 -> OpGe (loc x1))
--     <||> apA (ecTok LE_OP) (\x1 -> OpLe (loc x1))
--     <||> apA (ecChar '<') (\x1 -> OpLt (loc x1))
--     <||> apA (ecChar '=') (\x1 -> OpEq (loc x1))
--     <||> apA (ecTok AND_OP) (\x1 -> OpAnd (loc x1))
--     <||> apA (ecTok ANDA_OP) (\x1 -> OpAnda (loc x1))
--     <||> apA (ecChar '+') (\x1 -> OpPlus (loc x1))
--     <||> apA (ecChar '-') (\x1 -> OpMinus (loc x1))
--     <||> apA (ecTok CONS_OP) (\x1 -> OpCons (loc x1))
--     <||> apA (ecTok CAT_OP) (\x1 -> OpCat (loc x1))
--     <||> apA (ecTok UNION_OP) (\x1 -> OpUnion (loc x1))
--     <||> apA (ecTok INTER_OP) (\x1 -> OpInter (loc x1))
--     <||> apA (ecTok DISJ_OP) (\x1 -> OpDisj (loc x1))
--     <||> apA (ecTok IN_OP) (\x1 -> OpIn (loc x1))
--     <||> apA (ecTok SUBSET_OP) (\x1 -> OpSubset (loc x1))
--     <||> apA (ecTok DARROW) (\x1 -> OpImplies (loc x1))

ecBinExpr :: (MonadIO m,MonadCatch m) => EcParserT m (Expression Identifier Position)
ecBinExpr    = buildExpressionParser ecOpTable ecOpTerm
         <?> "expression"

ecOpTerm :: (MonadIO m,MonadCatch m) => EcParserT m (Expression Identifier Position)
ecOpTerm    =  ecAppExpr

ecOpTable :: (MonadIO m,MonadCatch m) => OperatorTable [TokenInfo] EcState (EcM m) (Expression Identifier Position)
ecOpTable   = [ 
             [prefix (ecChar '!') PreOpNot,prefix (ecChar '-') PreOpNeg]
           , [binary (ecTok CONS_OP) OpCons AssocLeft,binary (ecTok CAT_OP) OpCat AssocLeft,binary (ecTok UNION_OP) OpUnion AssocLeft,binary (ecTok INTER_OP) OpInter AssocLeft,binary (ecTok DISJ_OP) OpDisj AssocLeft,binary (ecTok IN_OP) OpIn AssocLeft,binary (ecTok SUBSET_OP) OpSubset AssocLeft]
           , [binary (ecChar '*') OpMul AssocLeft]
           , [binary (ecChar '+') OpPlus AssocLeft,binary (ecChar '-') OpMinus AssocLeft]
           , [binary (ecTok GE_OP) OpGe AssocLeft,binary (ecTok LE_OP) OpLe AssocLeft,binary (ecChar '<') OpLt AssocLeft,binary (ecChar '=') OpEq AssocLeft]
           , [binary (ecTok AND_OP) OpAnd AssocRight,binary (ecTok ANDA_OP) OpAnda AssocRight,binary (ecTok OR_OP) OpOr AssocRight]
           , [binary (ecTok DARROW) OpImplies AssocRight,binary (ecTok EQUIV) OpEquiv AssocRight]
           ]

prefix :: (MonadIO m,MonadCatch m) => EcParserT m TokenInfo -> (Position -> PreOp Identifier Position) -> Operator [TokenInfo] EcState (EcM m) (Expression Identifier Position)
prefix  name op = Prefix $ do
            tok <- name
            let p = loc tok
            return $ \e2 -> PreOpExpr p (Qualified p [] (op p)) e2
    

binary :: (MonadIO m,MonadCatch m) => EcParserT m TokenInfo -> (Position -> Op Identifier Position) -> Assoc -> Operator [TokenInfo] EcState (EcM m) (Expression Identifier Position)
binary  name op assoc = Infix (
    do
            tok <- name
            let p = loc tok
            return $ \e1 e2 -> BinOpExpr p e1 (Qualified p [] (op p)) e2
    ) assoc

ecBinOpLhs :: (MonadIO m,MonadCatch m) => EcParserT m (Op Identifier Position)
ecBinOpLhs = apA (ecTok CONS_OP) (\x1 -> OpCons (loc x1))
     

-- * Parsing functions

parseFileIO :: String -> IO (Program Identifier Position)
parseFileIO fn = runEcM $ parseFile fn

parseFile :: (MonadIO m,MonadCatch m) => String -> EcM m (Program Identifier Position)
parseFile fn = do
    str <- liftIO (readFile fn)
    parseEc fn str

parseEcIO :: String -> String -> IO (Program Identifier Position)
parseEcIO fn str = runEcM $ parseEc fn str

parseEc :: (MonadIO m,MonadCatch m) => String -> String -> EcM m (Program Identifier Position)
parseEc fn str = parseEcWith fn str (startPos fn) ecProgram

parseEcWith :: (MonadIO m,PP (EcM m) a) => String -> String -> Position -> EcParserT m a -> EcM m a
parseEcWith fn str pos parser = do
    case runLexerWith fn str (positionToAlexPos pos) return of
        Left err -> throwError $ LexicalError err
        Right toks -> do
            --liftIO $ hPutStrLn stderr ("Lexed " ++ fn ++ ":") >> hPutStrLn stderr (show $ map tSymb toks)
            e <- runParserT (setPosition (positionToSourcePos pos) >> parser) () fn toks
            case e of
                Left err -> throwError $ ParserError $ show err
                Right a -> do
                    ppa <- ppr a
                    --liftIO $ hPutStrLn stderr ("Parsed " ++ fn ++ ":") >> hPutStrLn stderr (ppa)
                    return a

ecPosition :: (Monad m,MonadCatch m) => EcParserT m Position
ecPosition = liftM sourcePosToPosition getPosition