{-| This module translates a GHC core 'ExternalCore.Module' to a list
    of 'CL.Clause'.  The GHC core module is supposed to have been
    already lifted (all function declarations and case expressions at 
    toplevel). -}

-- #ignore-exports, prune

module Core2Cl (core2cl) where

import Cl.Abs as Cl
import ExternalCore as C

import UnObfusc(unObfusc, obfusc)
 
import Maybe

import Monad
import Control.Monad.State

import Text.PrettyPrint.HughesPJ
import IO
import PprExternalCore

core2cl :: C.Module -> Cl.Module
core2cl (Module mname tdefs vdefgs) = Cl.Mod lc lp
    where (lc,lp) = foldl c2cDef ([],[]) vdefgs
          c2cDef (lcode,lprop) x = (lcode++lcode',lprop++lprop')
              where (lcode',lprop') = c2cTopLevelVdefg ctx x
          ctx = ctxEmpty mname (lDef vdefgs)

-- * Translation contexts

-- ** CaseExp

{-| 'CaseExp' are unfinished clauses (i.e. clauses with holes). They are 
    build and extended while going through the graph. -}

type CaseExp = ([Cl.Pat],[([Cl.Guard], Maybe Cl.Exp, [Cl.Local])])

csEmpty :: [CaseExp]
csEmpty = [([], [([], Nothing, [])])]

-- *** Updating 'CaseExp'

csExtPat :: [CaseExp] -> Cl.Pat -> [CaseExp]
csExtPat cs p = map (ceExtPat p) cs
    where ceExtPat p (ps, ds) = ((ps++[p]), ds)

ceAddGuard :: Cl.Guard -> CaseExp -> CaseExp
ceAddGuard g (ps,ds) = (ps, map (\ (gs, e, ls) -> (gs++[g], e, ls)) ds) 

csReplExp :: [CaseExp] -> (Cl.Exp, [(Cl.Pat, Cl.Exp)]) -> [CaseExp]
csReplExp cs (e,pes) = cs'
    where cs' = map (\ (ps,ds) -> (ps,map replExp ds)) cs
          replExp (gs,ce,ls) = (gs, Just e,ls')
              where ls' = case pes of 
                      [] -> ls 
                      _  -> (Loc (map (\ (p,e) -> Def p e) pes)):ls

csReplPat :: [CaseExp] -> Cl.Pat -> Cl.Pat -> [CaseExp]
csReplPat cs e p = cs'
    where cs'        = map (\ (ps,ds) -> (map replPat ps, ds)) cs
          replPat pt = if pt == e then p else pt

-- *** From 'CaseExp' to 'Clause'

{-| A 'CaseExp' translates to a list of clauses. Uncomplete 'CaseExp' are
    discarded (they should probably raise an error). -}

ceToClauses :: Cl.Id -> CaseExp -> [Cl.Clause]
ceToClauses id (ps, ds) = case ds of 
    []                    -> []
    (gs, Nothing, ls):ds' -> ceToClauses id (ps,ds')
    (gs, Just e, ls):ds'  -> 
        (Cl id ps gs e ls):(ceToClauses id (ps,ds'))

csToClauses :: Cl.Id -> [CaseExp] -> [Cl.Clause]
csToClauses id cs = case cs of 
    []     -> []
    ce:cs' -> (ceToClauses id ce) ++ (csToClauses id cs')

-- ** Substitutions
 
{-| We need to substitute identifier with patterns and expressions. 
    We use a substitution environment made by an associate list and just 
    traverse the structures. -} 

type SubstEnv = [(Cl.Id, Cl.Pat)]

substEmpty :: SubstEnv
substEmpty = []

{-| @substPat env p@ returns a pattern build from @p@ and where all 
    substitutions defined by @env@ have been performed. -} 
substPat :: SubstEnv -> Cl.Pat -> Cl.Pat
substPat env p = case p of
    Pvar id    -> fromMaybe p (lookup id env)
    Pcon id ps -> Pcon id (map (substPat env) ps)

{-| @substAdd env id p@ adds a substitution of identifier @id@ by 
    pattern @pat@ in @env@. The substitution is propagated down into 
    @env@. -}
substAdd :: SubstEnv -> Cl.Id -> Cl.Pat -> SubstEnv
substAdd env id p = (id,p):(map (\ (ei,ep) -> (ei, substPat [(id,p)] ep)) env)

-- ** Contexts

{-| Contexts are records containing:

      - the name of the current module,

      - a list of 'CaseExp',

      - a substitution environment,

      - a list of variables to erase (??)

      - a list of function symbols (is that still needed?) -}
data Context = C { modName  :: String,
                   cexps    :: [CaseExp],
                   subst    :: SubstEnv,
                   erase    :: [String],
                   funs     :: [String]
                 }

ctxEmpty :: String -> [String] -> Context
ctxEmpty m fs = C { modName = m, cexps = csEmpty, subst = substEmpty, 
                    erase = [], funs = fs }

ctxErase :: Context -> String -> Bool
ctxErase ctx v = elem v (erase ctx)

ctxAddErase :: Context -> String -> Context
ctxAddErase ctx v = ctx { erase = v:(erase ctx) }

ctxReplExp :: Context -> (Cl.Exp, [(Cl.Pat, Cl.Exp)]) -> Context
ctxReplExp ctx e = ctx { cexps = csReplExp (cexps ctx) e }

ctxAddSubst :: Context -> Cl.Id -> Cl.Pat -> Context
ctxAddSubst ctx id p = ctx'
    where ctx'   = ctx { cexps = cexps', subst = subst' }
          cexps' = map (\(ps,ds) -> (map (substPat subst') ps, ds)) (cexps ctx)
          subst' = substAdd (subst ctx) id p

ctxAddGuard :: Context -> Cl.Exp -> Context
ctxAddGuard ctx e = ctx { cexps = cexps' }
    where cexps' = map (ceAddGuard (Guard [e])) (cexps ctx)

ctxConcat :: [Context] -> Context -> Context
ctxConcat ctxs c0 = 
    foldl (\ c1 -> \c2 -> C { modName = modName c0,
                              cexps = (cexps c1) ++ (cexps c2),
                              subst = subst c0,
                              erase = erase c0,
                              funs = funs c0 }) 
    (ctxEmpty (modName c0) (funs c0)) ctxs

-- * From Core to Cl

c2cTopLevelVdefg :: Context -> Vdefg -> ([Cl.Clause], [PropCl])
c2cTopLevelVdefg ctx vdefg =
    case vdefg of 
    Rec vdefs   -> foldl c2cOne ([],[]) vdefs
        where c2cOne (l1,l2) x = (l1'++l1, l2'++l2)
                  where (l1',l2') = c2cTopLevelVdef ctx x
    Nonrec vdef -> c2cTopLevelVdef ctx vdef

c2cTopLevelVdef :: Context -> Vdef -> ([Cl.Clause], [PropCl])
c2cTopLevelVdef ctx ((mname, v), ty, e) = clauses
    where clauses = case v of 
              'p':'r':'o':'p':'z':'u':_ | isTypeProp ty -> 
					    ([], [c2pVdef ctx v e])
              _ -> (csToClauses (qualifyname (modName ctx) (mname,v)) 
                    (cexps ctx'), [])
          ctx' = c2cLambda ctx e 

-- ** Lambdas

{-| Lambdas should all be at toplevel. Processing a lambda consists in 
    adding a parameter in the parameter list of the current list of 
    'CaseExp', and calling ourselves recursively. When we have no more 
    lambdas, we start processing cases. -}
c2cLambda :: Context -> C.Exp -> Context
c2cLambda ctx e = case e of 
    Lam (Vb (v,Tapp (Tcon ("GHCziBase", "ZCTOrd")) _)) e -> 
        c2cLambda (ctxAddErase ctx v) e
    Lam (Vb (v,t)) e -> c2cLambda ctx' e
        where ctx' = ctx { cexps = csExtPat (cexps ctx) 
                           (Cl.Pvar (qualifyname (modName ctx) ("",v))) }
    Lam (Tb _) e     -> c2cLambda ctx e
    _ -> c2cCaseExp ctx e

-- ** Cases

{-| Case expression should be directly following the lambdas. When 
    processing cases, we have two possibilities:

        * we do case on a variable - we replace the variable by the binder
          in the pattern arguments of the context and process the right
          hand sides.

        * we do case on a boolean expression, this boolean expression becomes
          a guard.

    Others cases (case on a non-trivial, non-boolean expression) are errors,
    and should not occur.
    /The second case (guard) is not implemented yet!/ -}
c2cCaseExp :: Context -> C.Exp -> Context
c2cCaseExp ctx e = case e of
    Case e (v,Tapp (Tcon ("GHCziBase", "ZCTOrd")) _) [alt] -> ctx''
        where ctx'' = c2cAlt ctx' (qualifyname (modName ctx) ("",v)) alt
              ctx'  = ctxAddClassOrd ctx
    Case (Var (m,x)) (v,ty) alts -> ctx''
        where ctx'' = ctxConcat (map (c2cAlt ctx' 
                                      (qualifyname (modName ctx) 
                                       ("",v))) alts) ctx
              ctx'  = ctxAddSubst ctx (qualifyname (modName ctx) ("",v)) pat
              pat   = Cl.Pvar (qualifyname (modName ctx) ("",v))
-- {-
    Case e (v, Tcon ("GHCziBase", "Bool")) alts -> ctx'
        where ctx' = ctxConcat (map (c2cAltGuard ctx ce) alts) ctx
              ce   = case c2cExp ctx e of (ce, []) -> ce
-- -}
    _ -> ctxReplExp ctx (c2cExp ctx e)

c2cAlt :: Context -> Cl.Id -> Alt -> Context
c2cAlt ctx id alt = case alt of
    Acon (m,c) tb vb (App (Appt (Var ("GHCziErr", "patError")) _) _) -> 
        ctxEmpty (modName ctx) (funs ctx)
    Acon (m,c) tb vb e -> c2cCaseExp (ctxAddSubst ctx id pc) e 
        where pc = Cl.Pcon (qualifyname (modName ctx) (m,c)) binds
              binds = map (\ (v,ty) -> Cl.Pvar (qualifyname (modName ctx) 
                                                ("",v))) vb
    Alit l e   -> 
        error ("Core2Cl.c2cAlt: No literals in CL yet. Case branch was: " ++ 
               show alt)
    Adefault e -> 
        error ("Core2Cl.c2cAlf: No defaults in CL. Case branch was: " ++ 
               show alt)

c2cAltGuard :: Context -> Cl.Exp -> Alt -> Context
c2cAltGuard ctx ce alt = case alt of
    Acon ("GHCziBase",b) tb vb e -> c2cCaseExp ctx' e
        where ctx' = ctxAddGuard ctx ce'
              ce'  = if b == "True" then ce else (clNot ce)

-- ** Other expressions

c2cVdefg :: Context -> Vdefg -> [(Cl.Pat, Cl.Exp)] 
c2cVdefg ctx vdefg = case vdefg of 
    Rec vdefs   -> foldl (\l -> \x -> (c2cVdef ctx x)++l) [] vdefs
    Nonrec vdef -> c2cVdef ctx vdef

c2cVdef :: Context -> Vdef -> [(Cl.Pat, Cl.Exp)]
c2cVdef ctx ((mname, v), ty, e) = 
    (Cl.Pvar (qualifyname (modName ctx) ("",v)),e'):l
    where (e',l) = c2cExp ctx e

c2cExp :: Context -> C.Exp -> (Cl.Exp, [(Cl.Pat, Cl.Exp)])
c2cExp ctx e = case e of 
    Var (m,v)      -> (e', []) 
        where e' = 
               if ((m /= modName ctx) && (m /= "")) 
                  then Efun (qualifyname "" (m,v))
                  else if (elem v (funs ctx)) 
                       then Efun (qualifyname (modName ctx) (m,v)) 
                       else expOfPat Evar (substPat (subst ctx) pat)
              pat = Pvar (qualifyname (modName ctx) (m,v))
    Dcon (m,c)     -> (e', [])
        where e'  = expOfPat Evar (substPat (subst ctx) pat)
              pat = Pcon (qualifyname (modName ctx) (m,c)) []
    App (Var (m,v)) e2 -> (Eapp e1' e2', l2) 
        where e1' = expOfPat Efun (substPat (subst ctx) pat)
              pat = Pvar (qualifyname (modName ctx) (m,v))
              (e2', l2) = c2cExp ctx e2
    App e1 (Var (m,v)) | ctxErase ctx v -> c2cExp ctx e1
    App e1 e2      -> (Eapp e1' e2', l1 ++ l2) 
        where (e1', l1) = c2cExp ctx e1
              (e2', l2) = c2cExp ctx e2
    Appt e ty -> c2cExp ctx e
    Let v e        -> (e', l2)
        where (e', l) = c2cExp ctx e 
              l1      = c2cVdefg ctx v 
              l2      = l ++ l1
    Coerce t e     -> c2cExp ctx e
    Note s e       -> c2cExp ctx e
    Lit l          -> (Econ (c2cLit l), [])
    External s ty  -> error "Core2Cl.c2cExp: External not supported"
    Lam _b _e      -> error ("Core2Cl.c2cExp: Lambda - should be at toplevel. Expression is: "
                             ++ show e)
    Case e vb alts -> error "Core2Cl.c2cExp: Case - should be at toplevel"

c2cBind b = case b of
    Vb (v, t) -> Pvar (qualifyname "" ("",v))
    Tb _      -> error "No type binding"

-- For now, we keep the GHC encoding to evoid any problem with the prover.
-- The user is not supposed to look directly at the code anyway.

--c2cId :: C.Id -> String
--c2cId ident = unObfusc ident

c2cId :: C.Id -> String
c2cId ident = unObfusc ident

qualifyname modName (mname, id) = coreToPrelude fullName 
    where fullName | null mname = qname modName id
                   | otherwise  = qname mname   id

qname_obf :: String -> String -> Cl.Id
qname_obf mod nam = qname (obfusc mod) (obfusc nam)

qname :: String -> String -> Cl.Id
qname modul name = Qname (Ident modul) (Ident name)

c2cLit :: C.Lit -> Cl.Id
c2cLit l = case l of
    Lint      i t -> qname "" "0"
    Lrational r t -> qname "" "0."
    Lchar     c t -> qname "" "c"
    Lstring   s t -> qname "" s

c2cPatExp :: C.Exp -> [Cl.Pat] -> Cl.Pat
c2cPatExp e ps = case e of 
    Var (m,v)  -> Pvar (qualifyname "" ("", v))
    Dcon (m,c) -> Pcon (qualifyname "" ("", c)) ps


coreToPrelude :: Cl.Id -> Cl.Id
coreToPrelude v = case v of
    v | v == qname_obf "Data.Tuple" "(,)"     -> qname "" "Pair"
      | v == qname_obf "GHC.Base"   "&&"      -> qname "" "boolean_and"
      | v == qname_obf "GHC.Base"   "++"      -> qname "" "append"
      | v == qname_obf "GHC.Base"   ":"       -> qname "" "Cons"
      | v == qname_obf "GHC.Base"   "False"   -> qname "" "false"
      | v == qname_obf "GHC.Base"   "True"    -> qname "" "true"
      | v == qname_obf "GHC.Base"   "[]"      -> qname "" "Nil"
      | v == qname_obf "GHC.Base"   "not"     -> qname "" "not"
      | v == qname_obf "GHC.Base"   "||"      -> qname "" "or"
      | v == qname_obf "GHC.List"   "null"    -> qname "" "null"
      | v == qname_obf "GHC.List"   "reverse" -> qname "" "reverse"
      | otherwise                             -> v

clNot :: Cl.Exp -> Cl.Exp
clNot e = Eapp (Evar (qname "" "not")) e

expOfPat :: (Cl.Id -> Cl.Exp) -> Cl.Pat -> Cl.Exp
expOfPat con p = case p of 
    Pvar id    -> con id
    Pcon id ps -> foldl (\ e -> \ p -> Eapp e (expOfPat con p)) (Econ id) ps


ctxAddClassOrd :: Context -> Context
ctxAddClassOrd ctx = ctx { subst = subst1 }
    where subst1 = substAdd subst0 (qname "" "tpl3") (Pvar (qname "" "leq"))
          subst0 = subst ctx

lDef :: [Vdefg] -> [String]
lDef vdefgs = foldl lDefVdefg [] vdefgs
    where lDefVdefg l vdefg = case vdefg of
                              Rec vdefs   -> foldl lDefVdef l vdefs
                              Nonrec vdef -> lDefVdef l vdef
          lDefVdef l ((mname, v), ty, e) = v:l

-- * From Properties to CL

data Prop
  = ForAll (Cl.Exp -> Prop)
  | Exists (Cl.Exp -> Prop)
  | And Prop Prop
  | Or  Prop Prop
  | Not Prop
  | Equal Cl.Exp Cl.Exp
  | Using [Cl.Id] Prop
  | Inline Cl.Id
  | Ninline Cl.Id

type Disj = [Cl.Lit]
type Conj = [Disj]

isTypeProp :: Ty -> Bool
isTypeProp ty = 
    case ty of
    Tcon ("Property", "Prop") -> True
    _                         -> False

c2pVdef :: Context -> String -> C.Exp -> PropCl
c2pVdef ctx v e = Cl.Property (qualifyname (modName ctx) ("",v)) cs pclt pclf
    where pclt = map PCl clt
          pclf = map PCl clf
          (cst,clt) = evalState (clausify [] p) 0
          (cs,clf) = evalState (clausify [] (Not p)) 0
          p = toProp ctx e 

c2pReduce e = case e of 
    Appt e t -> c2pReduce e
    _        -> e 


-- ----------------
-- Names for property language combinators:

qname_property :: C.Id -> Cl.Id
qname_property op = qname_obf "Property" op

pOpEqual  = qname_property "==="
pOpAnd    = qname_property "/\\"
pOpOr     = qname_property "\\/"
pOpEquiv  = qname_property "<=>"
pOpImply  = qname_property "==>"
pOpUsing  = qname_property "using"
pOpForAll = qname_property "forAll"
pOpExists = qname_property "exists"
pOpNot    = qname_property "nt"
pOpDollar = qname_obf "GHC.Base" "$"

-- ----------------

toProp :: Context -> C.Exp -> Prop
toProp ctx e = 
    case c2pReduce e of
    App e1 e2 -> 
        case c2pReduce e1 of
        App e3 e4 -> 
            case c2pReduce e3 of
            Var (m,v) ->
                case qualifyname (modName ctx) (m,v) of
                op | op == pOpEqual  -> Equal (toPropExp ctx e4) 
                                              (toPropExp ctx e2)
                   | op == pOpAnd    -> And a b 
                   | op == pOpOr     -> Or  a b
                   | op == pOpEquiv  -> Or (And a b) (And (Not a) (Not b))
                   | op == pOpImply  -> Or (Not a) b
                   | op == pOpUsing  -> Using (toPropList ctx e4) b
                   | op == pOpDollar -> toProp ctx (App e4 e2)
                    where a = toProp ctx e4
                          b = toProp ctx e2
                _ -> error ("Core2Cl.toProp: Unrecognized name: " 
			    ++ m ++ "." ++ v)
        Var (m,v) ->
            case qualifyname (modName ctx) (m,v) of
            op | op == pOpForAll -> ForAll (toPropFun ctx e2)
               | op == pOpExists -> Exists (toPropFun ctx e2)
               | op == pOpNot    -> Not    (toProp    ctx e2)

            _ -> error "Not a valid property (1)"
        _ -> error "Not a valid property (2)"

    Var (m,v) -> Inline (qualifyname (modName ctx) (m,v))

    _ -> error ("Not a valid property: " ++ (render (pexp e)))

toPropExp :: Context -> C.Exp -> Cl.Exp
toPropExp ctx e = e' 
    where (e', l) = c2cExp ctx e

toPropList :: Context -> C.Exp -> [Cl.Id]
toPropList ctx e = 
    case c2pReduce e of 
    App e1 e2 -> 
        case c2pReduce e1 of 
        App e3 e4 -> 
            case c2pReduce e3 of 
            Dcon (m,v) -> 
                case qualifyname (modName ctx) (m,v) of
                Qname (Ident "") (Ident "Cons") -> 
		    (toQname ctx e4):(toPropList ctx e2)
                _ -> error ("Using: not a recognized constructor - " ++
                            m ++ "." ++ v)
            _ -> error ("Using: not a valid list of properties (1): " ++
                        (render (pexp (c2pReduce e3)))) 
        _ -> error "Using: not a valid list of properties (2)"
    Dcon (m,v) ->
        case qualifyname (modName ctx) (m,v) of
        Qname (Ident "") (Ident "Nil") -> []
    _ -> error "Using: not a valid list of properties (3)"
    
toQname :: Context -> C.Exp -> Cl.Id
toQname ctx e = 
    case c2pReduce e of 
    Var (m,v) -> qualifyname (modName ctx) (m,v)
    _ -> error "Using: not a var"

substProp :: String -> Cl.Exp -> Prop -> Prop
substProp v e p = case p of 
    ForAll f    -> ForAll (\ x -> substProp v e (f x))
    Exists f    -> Exists (\ x -> substProp v e (f x))
    And p1 p2   -> And (substProp v e p1) (substProp v e p2)
    Or p1 p2    -> Or (substProp v e p1) (substProp v e p2)
    Not p       -> Not (substProp v e p)
    Equal e1 e2 -> Equal (substExp v e e1) (substExp v e e2)
    Using pl p  -> Using pl (substProp v e p)
    Inline id   -> Inline id 
    Ninline id  -> Ninline id 

substExp :: String -> Cl.Exp -> Cl.Exp -> Cl.Exp
substExp v e exp = case exp of
    Evar (Qname _m (Ident i)) | i == v -> e
    Eapp e1 e2                -> Eapp (substExp v e e1) (substExp v e e2)
    e                         -> e

toPropFun :: Context -> C.Exp -> (Cl.Exp -> Prop)
toPropFun ctx e = case e of 
    Lam (Vb (v,t)) e' -> \ x -> substProp v x (toProp ctx e')
    Let vg e ->
            case e of
            Var (m,v) ->
                case vg of 
                Nonrec ((m,v'), t, e') -> 
                    if v == v' 
                       then toPropFun ctx e'
                       else error ("Not a var: " ++ (render (pexp e)))
                _ -> error ("Recursive def: " ++ (render (pexp e)))
            _ -> error ("Not a var: " ++ (render (pexp e)))
    _ -> error ("Not a lambda: " ++ (render (pexp e)))

clausify :: [Cl.Exp] -> Prop -> State Int ([Cl.Id],[Disj])
clausify vs p = case positive p of
    ForAll f -> 
        do id <- get
           put (id+1)
           let v = Cl.Evar (Qname (Ident "") (Ident ("_univ_" ++ show id)))
           clausify (v:vs) (positive (f v))
    Exists f -> 
        do id <- get
           put (id+1)            
           let skol = Efun (Qname (Ident "") (Ident ("_skol_" ++ show id)))
           clausify vs (positive (f (foldl (\ g -> \ x -> Eapp g x) skol vs)))
    And p1 p2 -> 
        do (xu,xs) <- clausify vs p1
           (yu,ys) <- clausify vs p2
           return (xu++yu, xs++ys)
    Or p1 p2 -> 
        do (xu,xs) <- clausify vs p1
           (yu,ys) <- clausify vs p2
           return (xu++yu,xs `cross` ys)
        where xs `cross` ys = [ x ++ y | x <- xs, y <- ys ]     
    Not (Equal e1 e2) -> return ([],[[Lneg e1 e2]])
    Equal e1 e2 -> return ([],[[Lpos e1 e2]])
    Using pl p -> 
        do (yu,ys) <- clausify vs p
           return (pl++yu, ys)
    Inline id -> return ([],[[Cl.Linline id]])
    Ninline id -> return ([],[[Cl.Lninline id]])

positive :: Prop -> Prop
positive p = case p of 
    Not (ForAll f)  -> Exists (nt . f) 
    Not (Exists f)  -> ForAll (nt . f)
    Not (And p1 p2) -> Or (positive (nt p1)) (positive (nt p2))
    Not (Or p1 p2)  -> And (positive (nt p1)) (positive (nt p2))
    Not (Not p)     -> positive p
    Not (Using pl p) -> Using pl (positive (nt p))
    Not (Inline id) -> Ninline id
    Not (Ninline id) -> Inline id
    ForAll f        -> ForAll f
    Exists f        -> Exists f
    And p1 p2       -> And (positive p1) (positive p2)
    Or p1 p2        -> Or (positive p1) (positive p2)
    Using pl p      -> Using pl (positive p)
    p               -> p

nt :: Prop -> Prop
nt (Not p) = p
nt p       = Not p
