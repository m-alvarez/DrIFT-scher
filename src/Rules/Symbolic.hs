module Rules.Symbolic(rules) where

import RuleUtils hiding (integer)
import Control.Monad (guard)
import qualified RuleUtils as RU
import Language.Haskell.Exts hiding (name, var)
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

call name args = foldl App (var name) args

symbolic nameVar suffix = call "symbolic" [ append (var nameVar) (string suffix) ]

append e1 e2 = InfixApp e1 (QVarOp $ UnQual $ Symbol "++") e2

integer i = Lit $ Int (fromIntegral i)
string s = Lit $ String s
unit name = call "symbolicRange" [integer 0, integer 0, string name]

var name = Hs.Var $ UnQual $ Ident name

bind bindingName boundExpr =
  Generator emptySrcLoc (PVar $ Ident bindingName) boundExpr

mkBinding objName fieldName =
  Generator emptySrcLoc namePat symbolicExpr
  where namePat = PVar (Ident fieldName)
        symbolicExpr = symbolic "name" fieldName
        objNameVar = var objName

symbolicBind name suffix =
  bind ("field" ++ suffix) $ symbolic name ("%" ++ suffix)

ctorWitness body =
  bind "ctor" $ symbolicRange "name" 0 0 ("%ctor=" ++ constructor body)

mkSymbolicDeclCase body nameVar =
  Do $ ctorWitness body : map (symbolicBind "name") fieldNames ++ [ ret ]
  where fieldNames =
          if null (labels body)
            then map show [1 .. length (types body)]
            else labels body
        ret = Qualifier $ call "return" [call (constructor body) 
                                              (map (var.("field"++)) fieldNames)]

symbolicRange nameVar i j suffix =
  call "symbolicRange" [integer i, integer j, append (var nameVar) (string suffix)]

icase expr cases =
  Case expr alts
  where alts = zipWith makeAlt [1 ..] cases
        makeAlt i exp =
          Alt emptySrcLoc 
              (PLit Signless $ Int i)
              (UnGuardedRhs exp)
              (BDecls [])

mkSymbolicDecl datatype =
  InsDecl $ FunBind [
      Match emptySrcLoc (Ident "symbolic") [PVar $ Ident "name"] Nothing rhs (BDecls [])
  ]
  where rhs = UnGuardedRhs $ 
                Do [ 
                  bind "tag" $ symbolicRange "name" 1 (length $ body datatype) "%tag",
                  Qualifier $ 
                    icase (var "tag") [ mkSymbolicDeclCase b "name" | b <- body datatype ]
                ]

userRuleSymbolic datatype@D{name = name, vars = vars, body = body} =
  text $ prettyPrint $ mkSymbolicDecl datatype

