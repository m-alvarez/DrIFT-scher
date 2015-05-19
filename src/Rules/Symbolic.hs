module Rules.Symbolic(rules) where

import Data.List
import RuleUtils
import Control.Monad (guard)
import RuleUtils as RU
import Language.Haskell.Exts hiding (name)
import qualified Language.Haskell.Exts as Hs

rules = [
    ("Symbolic", userRuleSymbolic, "Debugging", "Derive Symbolic for scher", Nothing)
    ]

{- datatype that rules manipulate :-


data Data = D {	name :: Name,			 -- type's name
			constraints :: [(Class,Var)],
			vars :: [Var],		 -- Parameters
			body :: [Body],
			derives :: [Class],	 -- derived classes
			statement :: Statement}  -- type of statement
	   | Directive				 --|
	   | TypeName Name			 --| used by derive (ignore)
		deriving (Eq,Show)

data Body = Body { constructor :: Constructor,
		    labels :: [Name], -- [] for a non-record datatype.
		    types :: [Type]} deriving (Eq,Show)

data Statement = DataStmt | NewTypeStmt deriving (Eq,Show)

type Name = String
type Var = String
type Class = String
type Constructor = String

type Rule = (Tag, Data->Doc)

-}

applyTypes typ [] = typ
applyTypes typ (t:ts) = applyTypes (TyApp typ t) ts

mkTypeUse datatype =
  applyTypes (TyCon (UnQual (Ident $ name datatype))) (map (TyVar . Ident) (vars datatype))

emptySrcLoc = SrcLoc { srcFilename = "", srcLine = 0, srcColumn = 0 }

nSymbolic = UnQual (Ident "Symbolic")

hasTypeVariables t =
  case t of
    RU.Arrow t1 t2 -> hasTypeVariables t1 || hasTypeVariables t2
    RU.LApply t l  -> hasTypeVariables t || any hasTypeVariables l
    RU.Var s -> True
    RU.Con s -> False
    RU.Tuple ts -> any hasTypeVariables ts
    RU.List t -> hasTypeVariables t

mkConstraint t = ClassA nSymbolic [typeToSrcType t]

typeToSrcType t =
  case t of
    RU.Arrow t1 t2 -> TyFun (typeToSrcType t1) (typeToSrcType t2)
    RU.LApply t ts -> applyTypes (typeToSrcType t) (map typeToSrcType ts)
    RU.Var s       -> TyVar (Ident s)
    RU.Con s       -> TyCon (UnQual (Ident s))
    RU.Tuple ts    -> TyTuple Boxed (map typeToSrcType ts)
    RU.List t      -> TyList (typeToSrcType t)

mkConstraintList body = do
  t <- types body
  guard $ hasTypeVariables t
  return $ mkConstraint t

mkContext datatype = do
  l <- body datatype
  mkConstraintList l

makeInstance datatype =
  InstDecl loc Nothing bindings ctx nSymbolic typ dec
  where ctx = mkContext datatype
        typ = [mkTypeUse datatype]
        dec = [mkSymbolicDecl datatype]
        loc = SrcLoc { srcFilename = "", srcLine = 0, srcColumn = 0 }
        bindings = []

patId name = PVar (Ident name)

symbolic arg = App (Hs.Var $ UnQual $ Ident "symbolic") arg

append e1 e2 = InfixApp e1 (QVarOp $ UnQual $ Ident "++") e2

mkBinding objName fieldName =
  Generator emptySrcLoc namePat symbolicExpr
  where namePat = (PVar (Ident fieldName))
        symbolicExpr = symbolic $ append objNameVar fieldNameStr
        objNameVar = Hs.Var $ UnQual $ Ident objName
        fieldNameStr = Lit $ String fieldName


mkSymbolicDeclCase body nameVar =
  Do $ map (mkBinding nameVar) fieldNames
  where fieldNames =
          if null (labels body)
            then map (("fld"++) . show) [1 .. length (types body)]
            else labels body

mkSymbolicDecl datatype =
    InsDecl $ FunBind [
        Match emptySrcLoc (Ident "symbolic") [PVar $ Ident "name"] Nothing rhs (BDecls [])
      ]
  where rhs = undefined --case (body datatype) of
    --block -> mkSymbolicDeclCase body "name"

userRuleSymbolic datatype@D{name = name, vars = vars, body = body} =
    undefined 

