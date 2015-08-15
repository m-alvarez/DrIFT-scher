module Rules.Symbolic(rules) where

import qualified RuleUtils as Utils
import Language.Haskell.Exts hiding (name, var)
import qualified Language.Haskell.Exts as Hs

rules = [
    ("Symbolic", userRuleSymbolic, "Debugging", "Derive Symbolic for scher", Nothing)
    ]

applyTypes :: Type -> [Type] -> Type
applyTypes typ [] = typ
applyTypes typ (t:ts) = applyTypes (TyApp typ t) ts

mkTypeUse :: Utils.Data -> Type
mkTypeUse datatype =
  applyTypes (TyCon (UnQual (Ident $ Utils.name datatype))) 
             (map (TyVar . Ident) (Utils.vars datatype))

emptySrcLoc :: SrcLoc
emptySrcLoc = SrcLoc { srcFilename = "", srcLine = 0, srcColumn = 0 }

nSymbolic :: QName
nSymbolic = UnQual (Ident "Symbolic")

mkContext :: Utils.Data -> Context
mkContext datatype =
  map (symbolicA . TyVar . Ident) (Utils.vars datatype)

symbolicA :: Type -> Asst
symbolicA typ = ClassA nSymbolic [typ]

call :: String -> [Exp] -> Exp
call name args = foldl App (var name) args

symbolic :: String -> String -> Exp
symbolic nameVar suffix = call "make" [ append (var nameVar) (string suffix) ]

append :: Exp -> Exp -> Exp
append e1 e2 = InfixApp e1 (QVarOp $ UnQual $ Symbol "++") e2

integer :: (Integral i) => i -> Exp 
integer i = Lit $ Int $ fromIntegral i

string :: String -> Exp
string s = Lit $ String s

var :: String -> Exp
var name = Hs.Var $ UnQual $ Ident name

bind :: String -> Exp -> Stmt
bind bindingName boundExpr =
  Generator emptySrcLoc (PVar $ Ident bindingName) boundExpr

symbolicBind :: String -> String -> Stmt
symbolicBind name suffix =
  bind ("field" ++ suffix) $ symbolic name ("%" ++ suffix)

mkSymbolicDeclCase :: Utils.Body -> Exp
mkSymbolicDeclCase body =
  Do $ map (symbolicBind "name") fieldNames ++ [ ret ]
  where fieldNames =
          if null (Utils.labels body)
            then map show [1 .. length (Utils.types body)]
            else Utils.labels body
        ret = Qualifier $ call "return" [call (Utils.constructor body) 
                                              (map (var.("field"++)) fieldNames)]

symbolicRange :: Exp -> Int -> Int -> String -> Exp
symbolicRange nameVar i j suffix =
  call "makeRange" [integer i, integer j, append nameVar (string suffix)]

icase :: Exp -> [Exp] -> Exp
icase expr cases =
  Case expr alts
  where alts = zipWith makeAlt [1 ..] cases
        makeAlt i e =
          Alt emptySrcLoc 
              (PLit Signless $ Int i)
              (UnGuardedRhs e)
              (BDecls [])

constructorChoice :: Exp -> [Utils.Body] -> Exp
constructorChoice nameVar constructors = 
  symbolicRange nameVar 1 (min (length constructors + 1) 3) ("%Constructor%" ++ constructorNames)
  where constructorNames = show $ map Utils.constructor constructors

mkSymbolicDecl :: Utils.Data -> InstDecl
mkSymbolicDecl datatype =
    InsDecl $ FunBind [
      Match emptySrcLoc (Ident "symbolic") [PVar $ Ident "name"] Nothing rhs (BDecls [])
    ]
  where nameVar = var "name"
        rhs = 
          UnGuardedRhs $ Do [ 
            bind "tag" $ constructorChoice nameVar (Utils.body datatype),
            if length (Utils.body datatype) == 1
            then Qualifier $ Case (call "(==)" []) 
                    [ Alt emptySrcLoc (PApp (UnQual $ Ident "True") []) (UnGuardedRhs $ mkSymbolicDeclCase b) (BDecls []) | b <- Utils.body datatype ]
            else Qualifier $ icase (var "tag") [ mkSymbolicDeclCase b | b <- Utils.body datatype ]
          ]

makeInstance :: Utils.Data -> Decl
makeInstance datatype =
  InstDecl emptySrcLoc Nothing bindings ctx nSymbolic typ dec
  where ctx = mkContext datatype
        typ = [mkTypeUse datatype]
        dec = [mkSymbolicDecl datatype]
        bindings = []

userRuleSymbolic :: Utils.Data -> Utils.Doc
userRuleSymbolic datatype@(Utils.D _ _ _ _ _ _) =
  Utils.text $ prettyPrint $ makeInstance datatype
userRuleSymbolic Utils.Directive = error "Cannot generate symbolic instance for a directive"
userRuleSymbolic (Utils.TypeName _) = error "Cannot generate symbolic instance for typename"

