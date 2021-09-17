module ML where

import Text.PrettyPrint as PP
import Pretty
import Location
import Syntax
import Parser
import Prelude hiding ((<>))

import Control.Monad.Reader
import Control.Monad.RWS hiding ((<>))
import Control.Monad.State as State

import System.IO
import System.Exit
import System.FilePath.Posix
import Data.Char

import Data.Map (Map(..))
import qualified Data.Map as Map
import Data.Set (Set(..))
import qualified Data.Set as Set
import Data.Maybe
import Data.List as List

--import Debug.Trace

data PPMState = PPMState { context :: [String], imports :: Set [String], isFlat :: Bool, ignores :: Set String }
    deriving (Eq,Show)

type PPM = RWS PPMState () (Bool,Doc)

withTheory :: TheoryName Identifier loc -> PPM a -> PPM a
withTheory (TheoryName _ n) m = local (\(PPMState ctx imports b is) -> PPMState (ctx ++ [n]) imports b is) m 
--withTheory (TheoryName _ n) m = local (\s -> s ++ "_" ++ n) m 

programToML :: Program Identifier loc -> PPM Doc
programToML ds = do
    ps <- mapM declarationToML ds
    return $ vcat ps
    
withIgnores :: Doc -> PPM Doc -> PPM Doc
withIgnores n m = do
    is <- asks ignores
    if Set.member (show n) is then return empty else m

declarationToML :: Declaration Identifier loc -> PPM Doc
declarationToML (OperatorDec _ o) = operatorDeclarationToML o
declarationToML (AbbrevDec _ o) = abbrevDeclarationToML o
declarationToML (TheoryDec _ t) = theoryDeclarationToML t
declarationToML (ExportDec _ t) = return empty
declarationToML (TypeDec _ t) = typeDeclarationToML t

inDecl :: Doc -> PPM a -> PPM a
inDecl n m = do
    old <- State.get
    State.put (False,n)
    a <- m
    State.put old
    return a

operatorDeclarationToML :: OperatorDeclaration Identifier loc -> PPM Doc
operatorDeclarationToML (OperatorDeclaration _ n targs sig body) = do
    ppn <- operatorNameToML n
    inDecl ppn $ withIgnores ppn $ do
        psig <- operatorSignatureToML sig
        pbody <- case body of
            Nothing -> return $ text "= Pervasive.witness" 
            Just e -> do
                ppe <- expressionToML e
                return $ text "=" $+$ nest 4 ppe 
        is_rec <- State.gets fst
        let let_str = if is_rec then "let rec" else "let"
        return $ text let_str <+> ppn <+> psig <+> pbody
    
abbrevDeclarationToML :: AbbrevDeclaration Identifier loc -> PPM Doc
abbrevDeclarationToML (AbbrevDeclaration _ n targs sig body) = do
    ppn <- operatorNameToML n
    inDecl ppn $ withIgnores ppn $ do
        psig <- operatorSignatureToML sig
        pbody <- case body of
            Nothing -> return empty
            Just e -> do
                ppe <- expressionToML e
                return $ text "=" $+$ nest 4 ppe 
        is_rec <- State.gets fst
        let let_str = if is_rec then "let rec" else "let"
        return $ text let_str <+> ppn <+> psig <+> pbody

operatorSignatureToML :: OperatorSignature Identifier loc -> PPM Doc
operatorSignatureToML (OperatorSignature _ args t) = do
    ppargs <- mapM operatorArgToML args
    ppt <- ppOpt t $ \s -> liftM (text ":" <+>) (typeToML s)
    return $ hsep ppargs <+> ppt

maybeTypeToML :: Maybe (Type Identifier loc) -> PPM Doc
maybeTypeToML Nothing = return empty
maybeTypeToML (Just t) = do
    ppt <- typeToML t
    return $ text ":" <+> ppt
    
ofTypesToML :: [Type Identifier loc] -> PPM Doc
ofTypesToML [] = return empty
ofTypesToML ts = do
    ppts <- mapM typeToML ts
    return $ text "of" <+> sepBy (text "*") ppts

operatorArgToML :: OperatorArg Identifier loc -> PPM Doc
operatorArgToML (OperatorArg _ vs t) = do
    ppt <- maybeTypeToML t
    ppvs <- forM vs $ \v -> do
        ppv <- lhsToML v
        return $ parens (ppv <+> ppt)
    return $ hsep ppvs

lhsToML :: Lhs Identifier loc -> PPM Doc
lhsToML (VarLhs _ v) = qualifiedVarNameToML v
lhsToML (ProdLhs _ vs) = do
    ppvs <- mapM lhsToML vs
    return $ parens (sepBy (text ",") ppvs)
lhsToML (BinOpLhs _ e1 o e2) = do
    pe1 <- lhsToML e1
    pe2 <- lhsToML e2
    po <- opToML pe1 pe2 o
    return $ po
lhsToML (AppLhs _ v es) = do
    ppv <- qualifiedOperatorNameToML v
    ppes <- mapM lhsToML es
    let sep xs = if not (List.null es) && isQualTypeOperator v then parens (sepBy (text ",") xs) else hsep xs
    return $ parens (ppv <+> sep ppes)
lhsToML (NilLhs _) = return $ text "List.Nil"
    
expressionToML :: Expression Identifier loc -> PPM Doc
expressionToML (LetExpr _ vs le e) = do
    ppvs <- lhsToML vs
    pple <- expressionToML le
    ppe <- expressionToML e
    return $ parens (text "let" <+> ppvs <+> text "=" <+> pple <+> text "in" $+$ ppe)
expressionToML (VarExpr _ n) = varNameToML n
expressionToML (WithExpr l ws) = do
    let ns = withPatternVarNames $ head ws
    ppns <- mapM varNameToML ns
    ppws <- mapM withPatternToML ws
    return $ text "begin match"  <+> sepBy (text ",") ppns <+> text "with" $+$ vcat ppws $+$ text "end"
expressionToML (AppExpr _ v es) = do
    ppv <- qualifiedOperatorNameToML v
    ppes <- mapM expressionToML es
    let sep xs = if not (List.null es) && isQualTypeOperator v then parens (sepBy (text ",") xs) else hsep xs
    return $ parens (ppv <+> sep ppes)
expressionToML (BinOpExpr _ e1 o e2) = do
    pe1 <- expressionToML e1
    pe2 <- expressionToML e2
    po <- qualOpToML pe1 pe2 o
    return $ parens po
expressionToML (PreOpExpr _ o e2) = do
    pe2 <- expressionToML e2
    po <- qualPreOpToML pe2 o
    return $ parens po
expressionToML (FunExpr _ ls e) = do
    pls <- mapM operatorArgToML ls
    pe <- expressionToML e
    return $ parens (text "fun" <+> hsep pls <+> text "->" <+> pe)
expressionToML (ProdExpr _ es) = do
    pes <- mapM expressionToML es
    prodExprToML pes
    --let pes' = map (\(i,e) -> text "nth" <> text (show i) <+> text "=" <+> e) $ zip [1..] pes
    --return $ text "{" <+> sepBy (text ";") pes' <+> text "}" 
    --return $ parens (sepBy (text ",") pes)
expressionToML (ProjExpr _ e i) = do
    pe <- expressionToML e
    projExprToML pe i
    --return $ pe <> text ".nth" <> text (show i)
expressionToML (LitExpr _ l) = literalToML l
expressionToML (GetExpr l xs i) = do
    expressionToML (AppExpr l (getOpName l) [xs,i])
expressionToML (SetExpr l xs i x) = do
    expressionToML (AppExpr l (setOpName l) [xs,i,x])
expressionToML (ModExpr l x) = do
    expressionToML (AppExpr l (modOpName l) [x])
expressionToML (NilExpr _) = return $ text "List.Nil" 
expressionToML (IfThenElseExpr _ c e1 e2) = do
    ppc <- expressionToML c
    ppe1 <- expressionToML e1
    ppe2 <- expressionToML e2
    return $ text "if" <+> ppc <+> text "then" <+> ppe1 <+> text "else" <+> ppe2
expressionToML (ForallExpr {}) = return $ parens $ text "Pervasive.witness"

projExprToML :: Doc -> Integer -> PPM Doc
projExprToML e 1 = return $ parens (text "fst" <+> e)
projExprToML e 2 = return $ parens (text "snd" <+> e)
--projExprToML e 1 = return $ parens (text "fst" <+> e)
--projExprToML e n = projExprToML (parens (text "snd" <+> e)) (n-1)

prodExprToML :: [Doc] -> PPM Doc
prodExprToML [] = return $ text "()"
prodExprToML xs = return $ parens $ sepBy (text ",") xs
--prodExprToML [x] = return $ parens (x)
--prodExprToML [x,y] = return $ parens (x <+> text "," <+> y)
--prodExprToML (x:xs) = do
--    pxs <- prodExprToML xs
--    return $ parens (x <+> text "," <+> pxs)

withPatternToML :: WithPattern Identifier loc -> PPM Doc
withPatternToML (WithPattern _ lhs e) = do
    pplhs <- mapM lhsToML (map snd lhs)
    ppe <- expressionToML e
    return $ text "|" <+> sepBy (text ",") pplhs <+> text "->" <+> ppe

literalToML :: Literal loc -> PPM Doc
literalToML (IntLit _ i) = return $ parens (text "Pervasive.mk_int" <+> text (show i))
literalToML (BoolLit _ True) = return $ text "Pervasive._true"
literalToML (BoolLit _ False) = return $ text "Pervasive._false"
literalToML (FloatLit _ _) = error $ "unsupported float"

qualifiedPreOpToML :: QualifiedPreOp Identifier loc -> PPM Doc
qualifiedPreOpToML = qualifiedToML preOpToML

preOpToML :: PreOp Identifier loc -> PPM Doc
preOpToML op = return $ text (camlVars $ preOpName op) 

qualPreOpToML :: Doc -> QualifiedPreOp Identifier loc -> PPM Doc
qualPreOpToML e2 op = do
    qop <- qualifiedPreOpToML op
    return $ qop <+> e2

qualOpToML :: Doc -> Doc -> QualifiedOp Identifier loc -> PPM Doc
qualOpToML e1 e2 op = error "unsupported qual op"

opToML :: Doc -> Doc -> Op Identifier loc -> PPM Doc
--opToML e1 e2 (OpGe l) = return $ e1 <+> text ">=" <+> e2
--opToML e1 e2 (OpLe l) = return $ e1 <+> text "<=" <+> e2
--opToML e1 e2 (OpLt l) = return $ e1 <+> text "<" <+> e2
--opToML e1 e2 (OpEq l) = return $ e1 <+> text "=" <+> e2
--opToML e1 e2 (OpAnd l) = return $ e1 <+> text "&&" <+> e2
--opToML e1 e2 (OpAnda l) = return $ e1 <+> text "&&" <+> e2
--opToML e1 e2 (OpPlus l) = return $ (text "Z.add" <+> e1 <+> e2)
--opToML e1 e2 (OpMinus l) = return $ (text "Z.sub" <+> e1 <+> e2)
--opToML e1 e2 (OpCons l) = return $ (text "Cons" <+> parens (e1 <+> text "," <+> e2))
--opToML e1 e2 (OpCat l) = return $ (text "concat" <+> e1 <+> e2)
--opToML e1 e2 (OpUnion l) = return $ (text "union" <+> e1 <+> e2)
--opToML e1 e2 (OpInter l) = return $ (text "intersect" <+> e1 <+> e2)
--opToML e1 e2 (OpDisj l) = return $ (text "disjoint" <+> e1 <+> e2)
--opToML e1 e2 (OpIn l) = return $ (text "mem" <+> e2 <+> e1)
--opToML e1 e2 (OpSubset l) = return $ (text "subset" <+> e1 <+> e2)
opToML e1 e2 op = do
    ppop <- pp op
    return $ text "unsupported op" <+> ppop

theoryDeclarationToML :: TheoryDeclaration Identifier loc -> PPM Doc
theoryDeclarationToML (TheoryDeclaration _ n ds) = withTheory n $ do
    pn <- theoryNameToML n
    withIgnores pn $ do
        ps <- mapM declarationToML ds
        flat <- asks isFlat
        let doc = if flat
                    then vcat ps
                    else text "module" <+> pn <+> text "= struct" $+$ nest 4 (vcat ps) $+$ text "end"
        return doc
--theoryDeclarationToML (TheoryDeclaration _ n ds) = withTheory n $ do
--    ps <- mapM declarationToML ds
--    return $ vcat ps

typeDeclarationToML :: TypeDeclaration Identifier loc -> PPM Doc
typeDeclarationToML (TypeDeclaration _ args n t) = do
    ppn <- typeNameToML n
    withIgnores ppn $ do
        ppargs <- if null args
            then return empty
            else typeArgsToML args
        ppt <- case t of
            Nothing -> return empty
            Just t -> do
                ppt <- typeBodyDeclarationToML t
                return $ text "=" <+> ppt
        return $ text "type" <+> ppargs <+> ppn <+> ppt 

dropPrefix :: Eq a => [a] -> [a] -> [a]
dropPrefix [] ys = ys
dropPrefix xs [] = []
dropPrefix (x:xs) (y:ys) = if x==y then dropPrefix xs ys else y:ys

dropImports :: Set [String] -> [String] -> [String]
dropImports is xs = Set.fold (\i xs -> dropPrefix i xs) xs is

qualifiedToML :: (a -> PPM Doc) -> Qualified Identifier loc a -> PPM Doc
qualifiedToML go (Qualified _ qn a) = do
    r <- ask
    pa <- go a
    return $ text (concat $ map (++".") $ dropPrefix (context r) $ dropImports (imports r) qn) <> pa
--qualifiedToML go (Qualified _ qn a) = do
--    local (\s -> concat $ map ("_"++) qn) (go a)

qualifiedVarNameToML :: QualifiedVarName Identifier loc -> PPM Doc
qualifiedVarNameToML = qualifiedToML varNameToML

qualifiedTypeNameToML :: QualifiedTypeName Identifier loc -> PPM Doc
qualifiedTypeNameToML = qualifiedToML typeNameToML

qualifiedOperatorNameToML :: QualifiedOperatorName Identifier loc -> PPM Doc
qualifiedOperatorNameToML = qualifiedToML operatorNameToML

infixOps :: String -> String
infixOps "[]" = "Nil"
infixOps "::" = "Cons"
infixOps "_.[_]" = "get"
infixOps "_.[_<-_]" = "set"
infixOps "`|_|" = "abs"
infixOps str = error $ "unsupported infix op " ++ str

getOpName :: loc -> QualifiedOperatorName Identifier loc
getOpName l = Qualified l [] $ OperatorName l "get"

setOpName :: loc -> QualifiedOperatorName Identifier loc
setOpName l = Qualified l [] $ OperatorName l "set"

modOpName :: loc -> QualifiedOperatorName Identifier loc
modOpName l = Qualified l [] $ OperatorName l "mod"

addRec :: PPM Doc -> PPM Doc
addRec m = do
    doc <- m
    State.modify $ \(b,n) -> if (doc==n) then (True,n) else (b,n)
    return doc

isQualTypeOperator :: Qualified Identifier loc (OperatorName Identifier loc) -> Bool
isQualTypeOperator (Qualified _ _ n) = isTypeOperator n

isTypeOperator :: OperatorName Identifier loc -> Bool
isTypeOperator (OperatorName _ n) = False
isTypeOperator (InfixOperatorName _ "[]") = True
isTypeOperator (InfixOperatorName _ _) = True
isTypeOperator (InfixBinOp _ (OpCons _)) = True
isTypeOperator (InfixBinOp _ op) = False
isTypeOperator (InfixPreOp _ n) = False

operatorNameToML :: OperatorName Identifier loc -> PPM Doc
operatorNameToML (OperatorName _ n) = addRec $ do
    return $ text (camlVars n)
operatorNameToML (InfixOperatorName _ n) = addRec $ do
    return $ text (camlVars $ infixOps n)
operatorNameToML (InfixBinOp _ n) = addRec $ do
    return $ text (camlVars $ opName n) 
operatorNameToML (InfixPreOp _ n) = addRec $ do
    return $ text (camlVars $ preOpName n) 

--addCtx :: PPM Doc -> PPM Doc
--addCtx m = do
--    ctx <- ask
--    if null ctx then m else m >>= \txt -> return (txt <> text ctx)

camlTypes :: String -> String
camlTypes t = case camlNames t of
    Nothing -> lowerName t
    Just n -> n

camlVars :: String -> String
camlVars n = case (camlNames n) of
    Nothing -> n
    Just n -> n

camlNames :: String -> Maybe String
camlNames "val" = Just "_val"
camlNames "false" = Just "_false"
camlNames "true" = Just "_true"
camlNames "and" = Just "_and"
camlNames "or" = Just "_or"
camlNames "to" = Just "_to"
camlNames n = Nothing

lowerName :: String -> String
lowerName [] = []
lowerName (x:xs) = if isUpper x then '_':x:xs else x:xs

theoryNameToML :: TheoryName Identifier loc -> PPM Doc
theoryNameToML (TheoryName _ n) = return $ text n

typeNameToML :: TypeName Identifier loc -> PPM Doc
typeNameToML (TypeName _ n) = {-addCtx $ -} return $ text (camlTypes n)

varNameToML :: VarName Identifier loc -> PPM Doc
varNameToML (VarName _ n) = addRec $ return $ text (camlVars n)

typeArgToML :: TypeArg Identifier loc -> PPM Doc
typeArgToML (TypeArg _ n) = do
    return $ text "'" <> text n
    
typeArgsToML :: TypeArgs Identifier loc -> PPM Doc
typeArgsToML ts = do
    pts <- mapM typeArgToML ts
    return $ parens (sepBy (text ",") pts)

typeBodyDeclarationToML :: TypeBodyDeclaration Identifier loc -> PPM Doc
typeBodyDeclarationToML (TySynDeclaration _ t) = typeToML t
typeBodyDeclarationToML (TyDataDeclaration _ cs) = do
    ppcs <- forM cs $ \(cn,t) -> do
        ppcn <- operatorNameToML cn
        ppt <- ofTypesToML t
        return $ text "|" <+> ppcn <+> ppt
    return $ nest 4 (vcat ppcs) 

prodTypeToML :: [Doc] -> PPM Doc
prodTypeToML [] = return $ text "unit"
prodTypeToML xs = return $ parens $ sepBy (text "*") xs
--prodTypeToML xs = do
--    error $ "prodTypeToML: " ++ show (hsep xs)
--prodTypeToML (x:xs) = do
--    pxs <- prodTypeToML xs
--    return $ parens (x <+> text "*" <+> pxs)

typeToML :: Type Identifier loc -> PPM Doc
typeToML (ProdType l ts) = do
    ppts <- mapM typeToML ts
    prodTypeToML ppts
    --return $ parens (sepBy (text ",") ppts) <+> text "tuple" <> text (show (length ts))
    --return $ parens (sepBy (text "*") ppts)
typeToML (VarType _ v) = typeArgToML v
typeToML (AppType _ args t) = do
    ppargs <- if null args
        then return empty
        else liftM (\x -> parens (sepBy (text ",") x)) $ mapM typeToML args
    ppt <- qualifiedTypeNameToML t
    return $ ppargs <+> ppt
typeToML (FunType _ t1 t2) = do
    pt1 <- typeToML t1
    pt2 <- typeToML t2
    return $ parens (pt1 <+> text "->" <+> pt2)

ecToML :: Bool -> [String] -> Maybe String -> Set String -> Set [String] -> FilePath -> FilePath -> IO ()
ecToML flat opens qual ignores imports infile outfile = do
    prog <- parseFileIO infile
    let (ml,_,_) = runRWS (programToML prog) (PPMState (maybeToList qual) imports flat ignores) (False,empty)
    let startqual = map (\q -> "module " ++ q ++ "= struct") $ maybeToList qual
    let endqual = map (\q -> "end") $ maybeToList qual
    let str = unlines $ map ("open "++) opens ++ startqual ++ [show ml] ++ endqual
    writeFile outfile str

ecToML_ :: FilePath -> IO ()
ecToML_ file = ecToML False [] Nothing Set.empty (Set.singleton [dropExtension file]) file (replaceExtension file "ml")
    
    



