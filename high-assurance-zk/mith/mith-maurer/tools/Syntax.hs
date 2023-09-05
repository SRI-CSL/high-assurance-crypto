{-# LANGUAGE ScopedTypeVariables, DeriveGeneric, TemplateHaskell, TypeFamilies, DeriveFoldable, DeriveTraversable, DeriveFunctor, MultiParamTypeClasses, DeriveDataTypeable, TypeSynonymInstances, FlexibleInstances #-}

module Syntax where

import Data.List as List
import Data.Traversable
import Data.Foldable as Foldable
import Data.Generics hiding (empty,Generic,GT)

import Text.PrettyPrint as PP

import GHC.Generics (Generic)

import Pretty
import Location
import Position

import Control.Monad

import Prelude hiding ((<>))

type Identifier = String

instance Monad m => PP m String where
    pp s = return $ text s
    
data TheoryName iden loc = TheoryName loc iden
  deriving (Read,Show,Data,Typeable,Eq,Ord,Generic)

instance Location loc => Located (TheoryName iden loc) where
    type LocOf (TheoryName iden loc) = loc
    loc (TheoryName l vd) = l
    
instance (PP m loc,PP m iden) => PP m (TheoryName iden loc) where
    pp (TheoryName _ kname) = pp kname
    
data TypeName iden loc = TypeName loc iden
  deriving (Read,Show,Data,Typeable,Eq,Ord,Generic)

instance Location loc => Located (TypeName iden loc) where
    type LocOf (TypeName iden loc) = loc
    loc (TypeName l vd) = l
    
instance (PP m loc,PP m iden) => PP m (TypeName iden loc) where
    pp (TypeName _ kname) = pp kname
    
data VarName iden loc = VarName loc iden
  deriving (Read,Show,Data,Typeable,Eq,Ord,Generic)

instance Location loc => Located (VarName iden loc) where
    type LocOf (VarName iden loc) = loc
    loc (VarName l vd) = l

instance (PP m loc,PP m iden) => PP m (VarName iden loc) where
    pp (VarName _ kname) = pp kname
    
data OperatorName iden loc = OperatorName loc iden | InfixOperatorName loc String | InfixBinOp loc (Op iden loc) | InfixPreOp loc (PreOp iden loc)
  deriving (Read,Show,Data,Typeable,Eq,Ord,Generic)

instance Location loc => Located (OperatorName iden loc) where
    type LocOf (OperatorName iden loc) = loc
    loc (OperatorName l vd) = l
    loc (InfixOperatorName l n) = l
    loc (InfixBinOp l n) = l
    loc (InfixPreOp l n) = l

instance (PP m loc,PP m iden) => PP m (OperatorName iden loc) where
    pp (OperatorName _ kname) = pp kname
    pp (InfixOperatorName _ n) = return $ text (show n)
    pp (InfixBinOp _ n) = do
        ppn <- pp n
        return $ parens ppn
    pp (InfixPreOp _ n) = do
        ppn <- pp n
        return $ text "[" <> ppn <> text "]"
    
data Qualified iden loc a = Qualified loc [iden] a
  deriving (Read,Show,Data,Typeable,Eq,Ord,Generic)

instance Location loc => Located (Qualified iden loc a) where
    type LocOf (Qualified iden loc a) = loc
    loc (Qualified l _ vd) = l
  
instance (PP m loc,PP m iden,PP m a) => PP m (Qualified iden loc a) where
    pp (Qualified _ ns a) = do
        pns <- mapM pp ns
        pa <- pp a
        let pns' = map (\x -> x <> text ".") pns
        return $ hcat pns' <> pa

type QualifiedOp iden loc = Qualified iden loc (Op iden loc)
type QualifiedPreOp iden loc = Qualified iden loc (PreOp iden loc)
type QualifiedVarName iden loc = Qualified iden loc (VarName iden loc)
type QualifiedTypeName iden loc = Qualified iden loc (TypeName iden loc)
type QualifiedTheoryName iden loc = Qualified iden loc (TheoryName iden loc)
type QualifiedOperatorName iden loc = Qualified iden loc (OperatorName iden loc)

type Program iden loc = [Declaration iden loc]

data Declaration iden loc
    = OperatorDec loc (OperatorDeclaration iden loc)
    | AbbrevDec loc (AbbrevDeclaration iden loc)
    | TheoryDec loc (TheoryDeclaration iden loc)
    | TypeDec loc (TypeDeclaration iden loc)
    | ExportDec loc (ExportDeclaration iden loc)
  deriving (Read,Show,Data,Typeable,Eq,Ord,Generic)

instance Location loc => Located (Declaration iden loc) where
    type LocOf (Declaration iden loc) = loc
    loc (OperatorDec l vd) = l
    loc (TheoryDec l dd) = l
    loc (TypeDec l kd) = l
    loc (ExportDec l d) = l
    updLoc (OperatorDec _ vd) l = OperatorDec l vd
    updLoc (TheoryDec _ dd) l = TheoryDec l dd
    updLoc (TypeDec _ kd) l = TypeDec l kd

instance (PP m loc,Location loc,PP m iden) => PP m [Declaration iden loc] where
    pp xs = do
        pxs <- mapM pp xs
        return $ vcat $ map (\x -> x $+$ text "\n") pxs

instance (PP m loc,Location loc,PP m iden) => PP m (Declaration iden loc) where
    pp (OperatorDec _ vd) = pp vd
    pp (AbbrevDec _ vd) = pp vd
    pp (TheoryDec _ dd) = pp dd
    pp (TypeDec _ kd) = pp kd
    pp (ExportDec _ e) = pp e

data TheoryDeclaration iden loc = TheoryDeclaration loc (TheoryName iden loc) [Declaration iden loc]
  deriving (Read,Show,Data,Typeable,Eq,Ord,Generic)
 
instance Location loc => Located (TheoryDeclaration iden loc) where
    type LocOf (TheoryDeclaration iden loc) = loc
    loc (TheoryDeclaration l _ _) = l
    updLoc (TheoryDeclaration _ n x) l = TheoryDeclaration l n x
 
instance (PP m loc,Location loc,PP m iden) => PP m (TheoryDeclaration iden loc) where
    pp (TheoryDeclaration _ kname xs) = do
        ppk <- pp kname
        pxs <- mapM pp xs
        return $ text "theory" <+> ppk <> text "." $+$ nest 4 (vcat pxs) $+$ text "end" <+> ppk <> text "."

data ExportDeclaration iden loc = ExportDeclaration loc (QualifiedTheoryName iden loc) 
  deriving (Read,Show,Data,Typeable,Eq,Ord,Generic)
 
instance Location loc => Located (ExportDeclaration iden loc) where
    type LocOf (ExportDeclaration iden loc) = loc
    loc (ExportDeclaration l _) = l
    updLoc (ExportDeclaration _ n) l = ExportDeclaration l n
 
instance (PP m loc,Location loc,PP m iden) => PP m (ExportDeclaration iden loc) where
    pp (ExportDeclaration _ kname) = do
        ppk <- pp kname
        return $ text "export" <+> ppk <> text "." 

type TypeArgs iden loc = [TypeArg iden loc]

instance (PP m loc,Location loc,PP m iden) => PP m (TypeArgs iden loc) where
    pp ts = do
        pts <- mapM pp ts
        return $ parens (sepBy (text ",") pts)

data TypeArg iden loc = TypeArg loc iden
  deriving (Read,Show,Data,Typeable,Eq,Ord,Generic)
  
instance Location loc => Located (TypeArg iden loc) where
    type LocOf (TypeArg iden loc) = loc
    loc (TypeArg l vd) = l
  
instance (PP m loc,Location loc,PP m iden) => PP m (TypeArg iden loc) where
    pp (TypeArg _ n) = do
        ppn <- pp n
        return $ text "'" <> ppn

data TypeDeclaration iden loc
    = TypeDeclaration loc (TypeArgs iden loc) (TypeName iden loc) (Maybe (TypeBodyDeclaration iden loc))
  deriving (Read,Show,Data,Typeable,Eq,Ord,Generic)
  
instance Location loc => Located (TypeDeclaration iden loc) where
    type LocOf (TypeDeclaration iden loc) = loc
    loc (TypeDeclaration l _ _ _) = l
  
instance (PP m loc,Location loc,PP m iden) => PP m (TypeDeclaration iden loc) where
    pp (TypeDeclaration _ args n t) = do
        ppargs <- if null args
            then return empty
            else pp args
        ppn <- pp n
        ppt <- case t of
            Nothing -> return empty
            Just t -> do
                ppt <- pp t
                return $ text "=" <+> ppt
        return $ text "type" <+> ppargs <+> ppn <+> ppt <> text "."

data TypeBodyDeclaration iden loc
    = TySynDeclaration loc (Type iden loc)
    | TyDataDeclaration loc [(OperatorName iden loc,[Type iden loc])]
  deriving (Read,Show,Data,Typeable,Eq,Ord,Generic)
  
instance Location loc => Located (TypeBodyDeclaration iden loc) where
    type LocOf (TypeBodyDeclaration iden loc) = loc
    loc (TySynDeclaration l  _) = l
    loc (TyDataDeclaration l _) = l
  
instance (PP m loc,Location loc,PP m iden) => PP m (TypeBodyDeclaration iden loc) where
    pp (TySynDeclaration _ t) = pp t
    pp (TyDataDeclaration _ cs) = do
        ppcs <- forM cs $ \(cn,t) -> do
            ppcn <- pp cn
            ppt <- if List.null t
                then return empty
                else liftM (sepBy $ text "&") (mapM pp t)
            return $ text "|" <+> ppcn <+> ppt
        return $ text "[" <+> nest 4 (vcat ppcs) <+> text "]"

data Type iden loc
    = ProdType loc [Type iden loc]
    | VarType loc (TypeArg iden loc)
    | AppType loc [Type iden loc] (QualifiedTypeName iden loc)
    | FunType loc (Type iden loc) (Type iden loc)
  deriving (Read,Show,Data,Typeable,Eq,Ord,Generic)

instance Location loc => Located (Type iden loc) where
    type LocOf (Type iden loc) = loc
    loc (ProdType l vd) = l
    loc (VarType l vd) = l
    loc (AppType l _ _) = l
    loc (FunType l _ _) = l
  
instance (PP m loc,Location loc,PP m iden) => PP m (Type iden loc) where
    pp (ProdType _ ts) = do
        ppts <- mapM pp ts
        return $ parens (sepBy (text " *") ppts)
    pp (VarType _ a) = pp a
    pp (AppType _ args t) = do
        ppargs <- if null args
            then return empty
            else liftM (\x -> parens (sepBy (text ",") x)) $ mapM pp args
        ppt <- pp t
        return $ ppargs <+> ppt
    pp (FunType _ t1 t2) = do
        pt1 <- pp t1
        pt2 <- pp t2
        return $ parens (pt1 <+> text "->" <+> pt2)

data OperatorDeclaration iden loc = OperatorDeclaration loc (OperatorName iden loc) (Maybe (TypeArgs iden loc)) (OperatorSignature iden loc) (Maybe (Expression iden loc))
  deriving (Read,Show,Data,Typeable,Eq,Ord,Generic)

instance Location loc => Located (OperatorDeclaration iden loc) where
    type LocOf (OperatorDeclaration iden loc) = loc
    loc (OperatorDeclaration l _ _ _ _) = l
  
instance (PP m loc,Location loc,PP m iden) => PP m (OperatorDeclaration iden loc) where
    pp (OperatorDeclaration _ n tyargs s e) = do
        ppn <- pp n
        pptys <- case tyargs of
            Nothing -> return empty
            Just tys -> do
                pts <- mapM pp tys
                return $ text "[" <> hsep pts <> text "]"
        pps <- pp s
        ppe <- ppOpt e $ \x -> liftM (\x -> text "=" $+$ nest 4 x) (pp x)
        return $ text "op" <+> ppn <+> pptys <+> pps <+> ppe <> text "."

data AbbrevDeclaration iden loc = AbbrevDeclaration loc (OperatorName iden loc) (Maybe (TypeArgs iden loc)) (OperatorSignature iden loc) (Maybe (Expression iden loc))
  deriving (Read,Show,Data,Typeable,Eq,Ord,Generic)

instance Location loc => Located (AbbrevDeclaration iden loc) where
    type LocOf (AbbrevDeclaration iden loc) = loc
    loc (AbbrevDeclaration l _ _ _ _) = l
  
instance (PP m loc,Location loc,PP m iden) => PP m (AbbrevDeclaration iden loc) where
    pp (AbbrevDeclaration _ n tyargs s e) = do
        ppn <- pp n
        pptys <- case tyargs of
            Nothing -> return empty
            Just tys -> do
                pts <- mapM pp tys
                return $ text "[" <> hsep pts <> text "]"
        pps <- pp s
        ppe <- ppOpt e $ \x -> liftM (\x -> text "=" $+$ nest 4 x) (pp x)
        return $ text "abbrev" <+> ppn <+> pptys <+> pps <+> ppe <> text "."

type OperatorArgs iden loc = [OperatorArg iden loc]

data OperatorSignature iden loc = OperatorSignature loc (OperatorArgs iden loc) (Maybe (Type iden loc))
  deriving (Read,Show,Data,Typeable,Eq,Ord,Generic)

instance Location loc => Located (OperatorSignature iden loc) where
    type LocOf (OperatorSignature iden loc) = loc
    loc (OperatorSignature l _ _) = l

instance (PP m loc,Location loc,PP m iden) => PP m (OperatorSignature iden loc) where
    pp (OperatorSignature _ args t) = do
        ppargs <- mapM pp args
        ppt <- ppOpt t $ \s -> liftM (text ":" <+>) (pp s)
        return $ hcat ppargs <+> ppt

data OperatorArg iden loc = OperatorArg loc [Lhs iden loc] (Maybe (Type iden loc))
  deriving (Read,Show,Data,Typeable,Eq,Ord,Generic)

instance Location loc => Located (OperatorArg iden loc) where
    type LocOf (OperatorArg iden loc) = loc
    loc (OperatorArg l _ _) = l

instance (PP m loc,Location loc,PP m iden) => PP m (OperatorArg iden loc) where
    pp (OperatorArg _ vs t) = do
        ppvs <- mapM pp vs
        ppt <- pp t
        return $ parens (hsep ppvs <+> ppt)

data Lhs iden loc 
    = VarLhs loc (QualifiedVarName iden loc)
    | ProdLhs loc [Lhs iden loc]
    | BinOpLhs loc (Lhs iden loc) (Op iden loc) (Lhs iden loc) 
    | AppLhs loc (QualifiedOperatorName iden loc) [Lhs iden loc]
    | NilLhs loc
  deriving (Read,Show,Data,Typeable,Eq,Ord,Generic)
    
instance Location loc => Located (Lhs iden loc) where
    type LocOf (Lhs iden loc) = loc
    loc (VarLhs l _) = l
    loc (ProdLhs l _) = l
    loc (BinOpLhs l _ _ _) = l
    loc (AppLhs l _ _) = l
    loc (NilLhs l) = l

instance (PP m loc,Location loc,PP m iden) => PP m (Lhs iden loc) where
    pp (VarLhs _ v) = pp v
    pp (ProdLhs _ vs) = do
        ppvs <- mapM pp vs
        return $ parens (sepBy (text ",") ppvs)
    pp (BinOpLhs _ e1 o e2) = do
        ppe1 <- pp e1
        ppo <- pp o
        ppe2 <- pp e2
        return $ ppe1 <+> ppo <+> ppe2
    pp (AppLhs _ c xs) = do
        ppc <- pp c
        ppxs <- mapM pp xs
        return $ parens (ppc <+> hsep ppxs)
    pp (NilLhs _) = return $ text "[]"

data Expression iden loc
    = LetExpr loc (Lhs iden loc) (Expression iden loc) (Expression iden loc)
    | WithExpr loc [WithPattern iden loc]
    | AppExpr loc (QualifiedOperatorName iden loc) [Expression iden loc]
    | VarExpr loc (VarName iden loc)
    | BinOpExpr loc (Expression iden loc) (QualifiedOp iden loc) (Expression iden loc)
    | PreOpExpr loc (QualifiedPreOp iden loc) (Expression iden loc)
    | ProjExpr loc (Expression iden loc) Integer
    | FunExpr loc (OperatorArgs iden loc) (Expression iden loc)
    | ProdExpr loc [Expression iden loc]
    | LitExpr loc (Literal loc)
    | GetExpr loc (Expression iden loc) (Expression iden loc)
    | SetExpr loc (Expression iden loc) (Expression iden loc) (Expression iden loc)
    | ModExpr loc (Expression iden loc)
    | IfThenElseExpr loc (Expression iden loc) (Expression iden loc) (Expression iden loc)
    | NilExpr loc 
    | ForallExpr loc (OperatorArgs iden loc) (Expression iden loc)
  deriving (Read,Show,Data,Typeable,Eq,Ord,Generic)
  
instance Location loc => Located (Expression iden loc) where
    type LocOf (Expression iden loc) = loc
    loc (LetExpr l _ _ _) = l
    loc (VarExpr l _) = l
    loc (WithExpr l _) = l
    loc (AppExpr l _ _) = l
    loc (BinOpExpr l _ _ _) = l
    loc (PreOpExpr l _ _) = l
    loc (FunExpr l _ _) = l
    loc (ForallExpr l _ _) = l
    loc (ProjExpr l _ _) = l
    loc (ProdExpr l _) = l
    loc (LitExpr l _) = l
    loc (GetExpr l _ _) = l
    loc (SetExpr l _ _ _) = l
    loc (ModExpr l _) = l
    loc (NilExpr l) = l
    loc (IfThenElseExpr l c e1 e2) = l
  
instance (PP m loc,Location loc,PP m iden) => PP m (Expression iden loc) where
    pp (LetExpr _ vs le e) = do
        ppvs <- pp vs
        pple <- pp le
        ppe <- pp e
        return $ parens (text "let" <+> ppvs <+> text "=" <+> pple <+> text "in" $+$ ppe)
    pp (VarExpr _ n) = pp n
    pp (WithExpr l ws) = do
        ppws <- mapM pp ws
        return $ nest 4 $ vcat ppws
    pp (AppExpr _ v es) = do
        ppv <- pp v
        ppes <- mapM pp es
        return $ parens (ppv <+> hsep ppes)
    pp (BinOpExpr _ e1 o e2) = do
        pe1 <- pp e1
        po <- pp o
        pe2 <- pp e2
        return $ pe1 <+> po <+> pe2
    pp (PreOpExpr _ o e2) = do
        po <- pp o
        pe2 <- pp e2
        return $ po <+> pe2
    pp (FunExpr _ ls e) = do
        pls <- mapM pp ls
        pe <- pp e
        return $ text "fun" <+> hcat pls <+> text "=>" <+> pe
    pp (ForallExpr _ ls e) = do
        pls <- mapM pp ls
        pe <- pp e
        return $ text "forall" <+> hcat pls <+> text "," <+> pe
    pp (ProdExpr _ es) = do
        pes <- mapM pp es
        return $ parens (sepBy (text ",") pes)
    pp (ProjExpr _ e i) = do
        pe <- pp e
        return $ pe <> text ".`" <> text (show i)
    pp (LitExpr _ l) = pp l
    pp (GetExpr _ xs i) = do
        ppxs <- pp xs
        ppi <- pp i
        return $ ppxs <> text ".[" <> ppi <> text "]"
    pp (SetExpr _ xs i x) = do
        ppxs <- pp xs
        ppi <- pp i
        ppx <- pp x
        return $ ppxs <> text ".[" <> ppi <> text " <- " <> ppx <> text "]"
    pp (ModExpr _ x) = do
        ppx <- pp x
        return $ text "`|" <> ppx <> text "|"
    pp (NilExpr _) = return $ text "[]"
    pp (IfThenElseExpr l c e1 e2) = do
        ppc <- pp c
        ppe1 <- pp e1
        ppe2 <- pp e2
        return $ text "if" <+> ppc <+> text "then" <+> ppe1 <+> text "else" <+> ppe2
  
data WithPattern iden loc = WithPattern loc [(VarName iden loc,Lhs iden loc)] (Expression iden loc) 
  deriving (Read,Show,Data,Typeable,Eq,Ord,Generic)
  
withPatternVarNames :: WithPattern iden loc -> [VarName iden loc]
withPatternVarNames (WithPattern _ ns _) = map fst ns
  
instance (PP m loc,Location loc,PP m iden) => PP m (WithPattern iden loc) where
    pp (WithPattern l ws e)   = do
        ppws <- forM ws $ \(v,l) -> do
            ppv <- pp v
            ppl <- pp l
            return $ ppv <+> text "=" <+> ppl
        ppe <- pp e
        return $ text "with" <+> (sepBy (text ",") ppws) <+> text "=>" <+> ppe
  
instance Location loc => Located (WithPattern iden loc) where
    type LocOf (WithPattern iden loc) = loc
    loc (WithPattern   l _ _) = l 
  
data PreOp iden loc
    = PreOpNot       loc
    | PreOpNeg loc
  deriving (Read,Show,Data,Typeable,Eq,Ord,Generic)

instance (PP m iden) => PP m (PreOp iden loc) where
    pp op = return $ text $ showPreOp op
    
parsePreOp :: Location loc => String -> Maybe (PreOp iden loc)
parsePreOp "!" = Just $ PreOpNot noloc
parsePreOp "-" = Just $ PreOpNeg noloc
parsePreOp s = Nothing
    
showPreOp :: PreOp iden loc -> String
showPreOp (PreOpNot   l)   = "!" 
showPreOp (PreOpNeg   l)   = "-" 

preOpName :: PreOp iden loc -> String
preOpName (PreOpNot   l)   = "not" 
preOpName (PreOpNeg   l)   = "neg" 

instance Location loc => Located (PreOp iden loc) where
    type LocOf (PreOp iden loc) = loc
    loc (PreOpNot   l) = l 
    loc (PreOpNeg   l) = l 
  
data Op iden loc
    = OpGe       loc
    | OpLt loc
    | OpLe       loc
    | OpEq loc
    | OpOr loc
    | OpOra loc
    | OpAnd loc
    | OpAnda loc
    | OpPlus loc
    | OpMinus loc
    | OpMul loc
    | OpCons loc
    | OpCat loc
    | OpUnion loc
    | OpInter loc
    | OpDisj loc
    | OpIn loc
    | OpSubset loc
    | OpImplies loc
    | OpEquiv loc
  deriving (Read,Show,Data,Typeable,Eq,Ord,Generic)

instance (PP m iden) => PP m (Op iden loc) where
    pp op = return $ text $ showOp op

parseOp :: Location loc => String -> Maybe (Op iden loc )
parseOp ">="        = Just (OpGe   noloc)   
parseOp "<="        = Just (OpLe   noloc)   
parseOp "<"         = Just (OpLt noloc)     
parseOp "="         = Just (OpEq noloc)     
parseOp "\\/"       = Just (OpOr noloc)    
parseOp "||"        = Just (OpOra noloc)   
parseOp "/\\"       = Just (OpAnd noloc)    
parseOp "&&"        = Just (OpAnda noloc)   
parseOp "+"         = Just (OpPlus noloc)   
parseOp "-"         = Just (OpMinus noloc)  
parseOp "*"         = Just (OpMul noloc)  
parseOp "::"        = Just (OpCons noloc)   
parseOp "++"        = Just (OpCat noloc)    
parseOp "`|`"       = Just (OpUnion noloc)  
parseOp "`&`"       = Just (OpInter noloc)  
parseOp "`\\`"      = Just (OpDisj noloc)   
parseOp "\\in"      = Just (OpIn noloc)     
parseOp "\\subset"  = Just (OpSubset noloc) 
parseOp "=>"        = Just (OpImplies noloc)
parseOp "<=>"       = Just (OpEquiv noloc)
parseOp s = Nothing
    
showOp :: Op iden loc -> String
showOp (OpGe   l)   = ">=" 
showOp (OpLe   l)   =  "<=" 
showOp (OpLt l) =  "<"
showOp (OpEq l) =  "="
showOp (OpOr l) =  "\\/"
showOp (OpOra l) =  "||"
showOp (OpAnd l) =  "/\\"
showOp (OpAnda l) =  "&&"
showOp (OpPlus l) =  "+"
showOp (OpMinus l) =  "-"
showOp (OpMul l) =  "*"
showOp (OpCons l) =  "::"
showOp (OpCat l) =  "++"
showOp (OpUnion l) =  "`|`"
showOp (OpInter l) =  "`&`"
showOp (OpDisj l) =  "`\\`"
showOp (OpIn l) =  "\\in"
showOp (OpSubset l) =  "\\subset"
showOp (OpImplies l) =  "=>"
showOp (OpEquiv l) =  "<=>"

opName :: Op iden loc -> String
opName (OpGe   l)   = "ge" 
opName (OpLe   l)   =  "le" 
opName (OpLt l) =  "lt"
opName (OpEq l) =  "eq"
opName (OpOr l) =  "or"
opName (OpOra l) =  "ora"
opName (OpAnd l) =  "and"
opName (OpAnda l) =  "anda"
opName (OpPlus l) =  "plus"
opName (OpMinus l) =  "minus"
opName (OpMul l) =  "mul"
opName (OpCons l) =  "Cons"
opName (OpCat l) =  "cat"
opName (OpUnion l) =  "union"
opName (OpInter l) =  "intersection"
opName (OpDisj l) =  "except"
opName (OpIn l) =  "mem"
opName (OpSubset l) =  "subset"
opName (OpImplies l) =  "implies"
opName (OpEquiv l) =  "equiv"
opName op = error $ "opName: " ++ showOp op
    
instance Location loc => Located (Op iden loc) where
    type LocOf (Op iden loc) = loc
    loc (OpGe   l) = l 
    loc (OpLt l) = l
    loc (OpLe   l) = l 
    loc (OpEq l) = l
    loc (OpOr l) = l
    loc (OpOra l) = l
    loc (OpAnd l) = l
    loc (OpAnda l) = l
    loc (OpPlus l) = l
    loc (OpMinus l) = l
    loc (OpMul l) = l
    loc (OpCons l) = l
    loc (OpCat l) = l
    loc (OpUnion l) = l
    loc (OpInter l) = l
    loc (OpDisj l) = l
    loc (OpIn l) = l
    loc (OpSubset l) = l
    loc (OpImplies l) = l
    loc (OpEquiv l) = l
    updLoc (OpGe   _) l = OpGe   l
    updLoc (OpLe   _) l = OpLe   l

data Literal loc
    = IntLit loc Integer
    | BoolLit loc Bool
    | FloatLit loc Double
  deriving (Read,Show,Data,Typeable,Eq,Ord,Generic)
  
instance Location loc => Located (Literal loc) where
    type LocOf (Literal loc) = loc
    loc (IntLit l _)    = l
    loc (BoolLit l _)   = l
    loc (FloatLit l _)  = l
    updLoc (IntLit _ x)    l = (IntLit l x)   
    updLoc (BoolLit _ x)   l = (BoolLit l x)  
    updLoc (FloatLit _ x)  l = (FloatLit l x) 
  
instance PP m loc => PP m (Literal loc) where
    pp (IntLit _ i) = return $ integer i
    pp (BoolLit _ True) = return $ text "true"
    pp (BoolLit _ False) = return $ text "false"
    pp (FloatLit _ f) = return $ text (show f)
    
prodType :: loc -> [Type iden loc] -> Type iden loc
prodType l [t] = t
prodType l xs = ProdType l xs

prodExpr :: loc -> [Expression iden loc] -> Expression iden loc
prodExpr l [t] = t
prodExpr l xs = ProdExpr l xs

prodLhs :: loc -> [Lhs iden loc] -> Lhs iden loc
prodLhs l [t] = t
prodLhs l xs = ProdLhs l xs

