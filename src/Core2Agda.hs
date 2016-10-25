{-| Translating a Haskell core abstract syntax, which has gone through
case-abstraction and lambda-lifting already, to Agda abstract syntax.

Authors: Patrik Jansson, Gregoire Hamon, Andreas Abel 

Naming scheme: Function <c>2<a> translates Core abstract syntax
concept <c> to Agda abstract syntax concept <a> -}

module Core2Agda(core2agda,aIdent) where

import AbsAlfa as A       -- Agda abstract syntax
import ExternalCore as C   -- GHC Core abstract syntax (from GHC suite)

import UnObfusc            -- Name unmangling (from GHC suite)

-- for debugging
import PprExternalCore     -- Pretty printer for core (form GHC suite)
import Debug.Trace

data Ctx = C { modName :: String } -- Name of the current module

undef :: String -> a
undef = error

{-| 'core2agda': 
    Main function, converting a Core module to an Agda package.

A core module is a triple of a module name 'mname' a list of data and
newtype definitions 'tdefs' and a list of recursive and non-recursive
value definitions 'vdefgs'.  This is transformed into a list of Agda
declarations whose first element 'typedefs' is a big mutual definition
of all types and whose remaining elements 'vdefs' are the transformed
value definitions.  The module name is used as context 'ctx' for all
subtransformations. -}

core2agda :: C.Module -> A.Module
core2agda (C.Module mname tdefs vdefgs) = --A.Module decls
  A.Module [noattrdef ctx $ A.Package (id2aid mname) [] $ PackageDef decls]
  where ctx       = C { modName = mname } 
        decls     = map (noattrdef ctx) defs
        defs      = maybe vdefs (: vdefs) mtypedefs
        mtypedefs = mutual (map (tdef2def ctx) tdefs)
        vdefs     = map (vdefg2def ctx) vdefgs


{- 'noattrdef': Wrapper for an Agda definition.  

Produces a "definition" declaration in Agda with no special attributes
(such as 'Private', 'Public', 'Abstract', 'Concrete'.  The only other
declaration form is an 'Import' statement. -}

noattrdef :: Ctx -> A.Def -> A.Decl
noattrdef ctx = DDef []

{- 'mutual': Wrapper for a 'Mutual' Agda definition.

Produces a "Mutual" definition from a list of definitions.  If the
list is a singleton, the keyword mutual is not required.  If the list
is empty, nothing is returned. -}

mutual :: [A.Def] -> Maybe A.Def
mutual []  = Nothing
mutual [a] = Just a
mutual l   = Just $ Mutual l

{- 'vdefg2def': Transformation of value definitions:

A single recursive and a non-recursive value definition are both
translated in oridinary Agda definitions, whereas a bunch of recursive
values is translated into a 'Mutual' Agda declaration. -}

vdefg2def :: Ctx -> C.Vdefg -> A.Def
vdefg2def ctx vdefg = case vdefg of
    Rec [vdef]  -> vdef2def ctx vdef
    Rec vdefs   -> Mutual (map (vdef2def ctx) vdefs)
    Nonrec vdef -> vdef2def ctx vdef

{- 'vdef2def': A single value definition:

>  mod.var :: ty = exp  

is translated as such, where the qualified name 'mod.var' modified by
'qvar2aid' which 'unObfusc'ates it and subtracts the qualification if
it is a name local to this module. -}

vdef2def :: Ctx -> C.Vdef -> A.Def
vdef2def ctx ((mod, var), ty, exp) = Value id [] et ev
    where id = qvar2aid ctx (mod, var)
          et = ty2exp ctx ty
          ev = exp2exp ctx exp

{- 'tdef2def': Translate Core type definitions into Agda

A core type definition can be of one of the following forms:

> 1  data    Mod.T as = C_1 as_1 Ts_1 | ... | C_n as_n Ts_n
> 2  newtype Mod.T as = T
> 3  newtype Mod.T as

Form 1 (where the as_i are existentially bound type variables) is
translated into a corresponding Agda data declaration.  On the GHC
core level, a newtype is just a type synonym, so we translate it into
a Agda definition.  The third form becomes a axiomatically declared
set in Agda. -}

tdef2def :: Ctx -> C.Tdef -> A.Def
tdef2def ctx tdef = case tdef of

    C.Data  qtcon tbinds cdefs     -> A.Data aident typings constructors
        where aident       = qtcon2aid ctx qtcon
              typings      = map (tbind2typing ctx) tbinds
              constructors = map (cdef2cons ctx) cdefs            

    Newtype qtcon tbinds (Just ty) -> A.Type aident typings rhs -- or Value?
        where aident       = qtcon2aid ctx qtcon
              typings      = map (tbind2typing ctx) tbinds
              rhs          = ty2exp ctx ty

{- A: the old code translates a newtype as data which is
         inconsistent with the handling of newtype in core.

    Newtype qtcon tbinds (Just ty) -> A.Data aident typings constructors
        where aident       = qtcon2aid ctx qtcon
              typings      = map (tbind2typing ctx) tbinds
              constructors = [cdef2cons ctx (Constr qtcon [] [ty])]
-}

    Newtype qtcon tbinds Nothing   -> Axiom aident typings ESet
        where aident  = qtcon2aid ctx qtcon
              typings = map (tbind2typing ctx) tbinds

{- 'cdef2cons': Translating a constructor clause form a Core data
declaration into a matching Agda one.  A constructor
@
  C T1 ... Tn
@
is translated into (modulo unmangling of name C)
@ 
  C (x1::T1) ... (xn::Tn)
@
where the xi are 'dummys'.
-}

cdef2cons :: Ctx -> C.Cdef -> A.Constructor
cdef2cons ctx (Constr qdcon [] tys) = Cnstr aident typings
  where aident  = qdcon2aid ctx qdcon
        typings = zipWith (ty2typing ctx) dummys tys 
  -- Wrong: perhaps corrected 
  -- A: ^what does this comment mean?
cdef2cons _ _ = error "cdef2cons: Do not know how to translate existential data type constructors."

-- Name handling

-- 'dummys' is the infinite variable supply "x1","x2",...
dummys :: [Id]
dummys = map (('x':).show) [1..]

-- unobfuscate a qualified identified
unObfuscQual :: Qual Id -> Qual Id
unObfuscQual (mname, id) = (unObfusc mname, unObfusc id)

-- print a qualified identifier as string.  The local names get unqualified
qualify :: Ctx -> Qual Id -> String
qualify ctx (mname, id) = 
    case mname of
    ""                     -> id
    s | (modName ctx) == s -> id
    s                      -> s ++ "." ++ id

{-
qualifySomething :: (String -> String) -> Ctx -> Qual Id -> Id
qualifySomething f ctx (mname, id) = f fullName 
    where fullName = 
              case mname of
              ""                     -> unObfusc id
              s | (modName ctx) == s -> unObfusc id
              s                      -> (unObfusc s) ++ "." ++ (unObfusc id)

qualifyname :: Ctx -> Qual Id -> Id
qualifyname ctx (mname, id) = qualifySomething valueId2string ctx (mname, id)

qualifyTcon :: Ctx -> Qual Tcon -> Id
qualifyTcon ctx (mname, id) = qualifySomething typeId2string ctx (mname, id)
-}

-- convert qualified type identifiers
qtcon2aid :: Ctx -> Qual Tcon -> AIdent
qtcon2aid ctx = aIdent . typeId2string . (qualify ctx) . unObfuscQual

-- convert qualified value identifiers
qvar2aid  :: Ctx -> Qual Id -> AIdent
qvar2aid ctx  = aIdent . valueId2string . (qualify ctx) . unObfuscQual

-- convert qualified data constructors (synonym)
qdcon2aid :: Ctx -> Qual Dcon -> AIdent
qdcon2aid = qvar2aid

-- turn non-qualified non-prelude identifiers into Agda ids.
id2aid :: Id -> AIdent
id2aid = aIdent . unObfusc

var2aid :: Ctx -> Var -> AIdent
var2aid ctx = id2aid 

tvar2aid :: Ctx -> Tvar -> AIdent
tvar2aid ctx = id2aid 

-- create Agda identifier without position information
aIdent :: String -> AIdent
aIdent id = F (PIdent ((-1,-1), id))

nameVariant :: String -> AIdent -> AIdent
nameVariant prefix (F (PIdent (_pos, x))) = aIdent (prefix ++ x)

-- typed bindings
ty2typing :: Ctx -> Id -> Ty -> Typing
ty2typing ctx name ty = TDecl (VDecl [BVar $ id2aid name] (ty2exp ctx ty))

-- Embed types as Agda expressions
ty2exp :: Ctx -> Ty -> A.Exp
ty2exp ctx ty = case ty of 
    Tvar tvar        -> EVar (tvar2aid  ctx tvar)
    Tcon qtcon       -> EVar (qtcon2aid ctx qtcon)
    Tapp (Tapp (Tcon fun) ty1) ty2 | fun == tcArrow 
                     -> EFun et AShow ev
        where et      = ty2exp ctx ty1 
              ev      = ty2exp ctx ty2
    Tapp ty1 ty2     -> EApp (ty2exp ctx ty1) (ty2exp ctx ty2) 
    Tforall tbind ty -> forall2pi ctx tbind (ty2exp ctx ty)

-- Translate quantification over types as quantification over inhabited types
-- (forall a:*. t)' = (a::Set) -> (|ia::Inhabited a) -> t'
-- (forall a:k. t)' = (a::k' ) -> t'

forall2pi :: Ctx -> Tbind -> A.Exp -> A.Exp
forall2pi ctx tbind@(_, Karrow _ _) = EPi (tbind2vardecl ctx tbind) AShow
forall2pi ctx tbind@(var, _star)    = EPi (tbind2vardecl ctx tbind) AShow .
      EPi (VDecl [BVar (nameVariant "inhabited_" (id2aid var))]
                 (EVar (id2aid "Inhabited") `EApp` EVar (id2aid var))) AHide

tbind2typing  :: Ctx -> Tbind -> Typing
tbind2typing ctx = TDecl . (tbind2vardecl ctx)

tbind2vardecl :: Ctx -> Tbind -> VarDecl
tbind2vardecl ctx (tvar,kind) = VDecl [BVar id] e
    where id = id2aid tvar 
          e  = kind2exp ctx kind

vbind2vardecl :: Ctx -> Vbind -> VarDecl
vbind2vardecl ctx (var,ty) = VDecl [BVar (var2aid ctx var)] (ty2exp ctx ty)

bind2vardecl :: Ctx -> Bind -> VarDecl
bind2vardecl ctx bind =
    case bind of
    Vb vbind -> vbind2vardecl ctx vbind
    Tb tbind -> tbind2vardecl ctx tbind

tbind2aident :: Ctx -> Tbind -> AIdent
tbind2aident ctx (tvar,_kind) = tvar2aid ctx tvar

vbind2aident :: Ctx -> Vbind -> AIdent
vbind2aident ctx (var, _ty)   = var2aid ctx var

kind2exp :: Ctx -> Kind -> A.Exp
kind2exp ctx kind = case kind of
    Klifted            -> ESet -- an approximation 
    Kunlifted          -> ESet -- an approximation 
    Kopen              -> ESet -- an approximation 
    Karrow kind1 kind2 -> EFun (kind2exp ctx kind1) AShow (kind2exp ctx kind2)

-- | 'wildcard' currently only used to translate 'External'
wildcard :: A.Exp
wildcard = EMeta $ Meta ((-1,-1), "WILD_HONEY") 
  -- the placeholder comes in handy (;-)

patError :: A.Exp
patError = EVar (id2aid "error")

-- | Translate Core expression to Agda expression.
exp2exp :: Ctx -> C.Exp -> A.Exp
exp2exp ctx e = case e of 
    Var ("GHCziErr", "patError") -> patError
    Var qvar            -> EVar (qvar2aid ctx  qvar)
    Dcon qdcon          -> ECon (qdcon2aid ctx qdcon)
    Lit lit             -> lit2exp ctx lit
    App exp1 exp2       -> EApp exp1' (exp2exp ctx exp2) 
{-
                           case exp1' of
            EVar (F (PIdent "?")) -> exp1'
            _                    -> EApp exp1' (exp2exp ctx exp2) 
-}
        where exp1'      = exp2exp ctx exp1
    Appt exp ty         -> case exp' of
--            EVar (F (PIdent "GHC.Err.patError")) -> patError
            ECon qd                             -> exp'
            _                                   -> EApp exp' (ty2exp ctx  ty) 
        where exp'       = exp2exp ctx exp
    Lam bind exp        -> lam2abs ctx bind body 
        where -- binder     = bind2vardecl ctx bind
              body       = exp2exp ctx exp
    Let vdefg exp       -> ELet locdef body
        where locdef     = [noattrdef ctx (vdefg2def ctx vdefg)]
              body       = exp2exp ctx exp
    Case exp vbind alts -> ECase (EVar var') branchs
        where (var,ty)   = vbind
              var'       = var2aid ctx var
              decl       = noattrdef ctx (Value var' [] (ty2exp ctx ty) 
                                            (exp2exp ctx exp))
              branchs    = map (alt2branch ctx) alts
    Coerce ty exp       -> exp2exp ctx exp
--    Coerce ty exp       -> wildcard 
    Note string exp     -> exp2exp ctx exp
    External string ty  -> wildcard 

-- Translate quantification over types as quantification over inhabited types
-- (forall a:*. t)' = (a::Set) -> (|ia::Inhabited a) -> t'
-- (forall a:k. t)' = (a::k' ) -> t'

lam2abs :: Ctx -> Bind -> A.Exp -> A.Exp
lam2abs ctx bind@(Tb (_,Karrow _ _)) = EAbs (bind2vardecl ctx bind) AShow
lam2abs ctx bind@(Vb (_, _))         = EAbs (bind2vardecl ctx bind) AShow
lam2abs ctx bind@(Tb (var, _star))   = EAbs (bind2vardecl ctx bind) AShow .
      EAbs (VDecl [BVar (nameVariant "inhabited_" (id2aid var))]
                 (EVar (aIdent "Inhabited") `EApp` EVar (id2aid var))) AHide

alt2branch :: Ctx -> Alt -> Branch
alt2branch ctx alt = case alt of
    Acon qdcon tbinds vbinds exp -> BranchCon aident aidents exp'
        where exp'    = exp2exp ctx exp
              aident  = qdcon2aid ctx qdcon
              aidents = map (tbind2aident ctx) tbinds ++ 
                        map (vbind2aident ctx) vbinds
    Alit lit exp -> BranchCon (undef "alt2branch: Literals not implemented") 
                    (undef "alt2branch: Literals not implemented") 
                    (exp2exp ctx exp)
    Adefault exp -> BranchVar dummy (exp2exp ctx exp)

dummy :: AIdent
dummy = id2aid "dummy1738"

--  There should (probably) be a type of literals in Agda
--  The type should be checked
lit2exp :: Ctx -> C.Lit -> A.Exp
lit2exp ctx lit = case lit of
    Lint i  _ty     -> EInt i
    Lrational r _ty -> EDouble (fromRational r) 
    -- should have a constructor in Agda
    Lchar c _ty     -> EChar c
    Lstring s  _ty  -> EString s

typeId2string t = case t of
    "Data.Maybe.Maybe" -> "Maybe"
    "Data.Tuple.(,)"   -> "Pair"
    "Data.Tuple.(,,)"  -> "Triple"
    "GHC.Base.Bool"    -> "Bool"
    "GHC.Base.Char"    -> "Char"
    "GHC.Base.[]"      -> "List"
    "GHC.Base.()"      -> "Unit"
    "GHC.Num.Integer"  -> "Integer"
    "Property.Prop"    -> "Property.Prop"
    s                  -> s

valueId2string v = case v of

-- general
    "GHC.Base.$"         -> "($)"  
    "GHC.Base.."         -> "compose"  

-- Maybe 
    "Data.Maybe.Just"    -> "Just"
    "Data.Maybe.Nothing" -> "Nothing"

-- Tuples
    "Data.Tuple.(,)"     -> "Pair"
    "Data.Tuple.(,,)"    -> "Triple"

-- Unit
    "GHC.Base.()"        -> "tt@_"

-- Lists
    "GHC.Base.[]"        -> "Nil"
    "GHC.Base.:"         -> "(:)"
    "GHC.Base.++"        -> "append"
    "GHC.Base.map"       -> "map"
    "GHC.List.null"      -> "null"
    "GHC.List.reverse"   -> "reverse"

-- Booleans
    "GHC.Base.False"     -> "False"
    "GHC.Base.True"      -> "True"
    "GHC.Base.not"       -> "not"
    "GHC.Base.||"        -> "(||)"
    "GHC.Base.&&"        -> "(&&)"

-- Properties
    "Property.==="       -> "Property.(===)"
    "Property.forAll"    -> "Property.forAll"
    "Property.exists"    -> "Property.exists"
    "Property./\\"       -> "Property.(/\\)"
    "Property.\\/"       -> "Property.(\\/)"
    "Property.<=>"       -> "Property.(<=>)"
    "Property.==>"       -> "Property.(==>)"
    "Property.true"      -> "Property.true"
    "Property.false"     -> "Property.false"
    "Property.nt"        -> "Property.nt"
    "Property.holds"     -> "Property.holds"
    "Property.holdsNot"  -> "Property.holdsNot"
    -- using not implementable in Agda


-- default
    s                    -> s
