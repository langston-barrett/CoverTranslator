{-| Lambda Lifting for GHC Core

    The algorithm is due to Danvy and Schultz and described in
    "Lambda-Lifting in Quadratic Time" - BRICS RS-02-30.

    The main function applies 3 transformations in turn:

       1. Naming anonymous functions

       2. Parameter lifting: closing all function definitions

       3. Block floating: moving the function definitions to the top level
-}

module LambdaLifting (lambdaLift) where

import Maybe
import List(sortBy)

import Monad
import Control.Monad.State

import Data.Graph
import Data.Tree
import Data.Set

import ExternalCore
import PprExternalCore()

-- import Hugs.Observe

lambdaLift :: Module -> Module
lambdaLift m = bfModule (plModule (nameModule m))

-- Abbreviations

funType :: Ty -> Ty -> Ty
funType t1 t2 = Tapp (Tapp (Tcon tcArrow) t1) t2

-- Env definitions

varOfBind :: Bind -> Var
varOfBind (Vb (v, ty)) = v
varOfBind (Tb (v, k))  = v

instance Eq Bind where
    b1 == b2 = (varOfBind b1) == (varOfBind b2)

instance Ord Bind where
    compare b1 b2 = compare (varOfBind b1) (varOfBind b2)

orderBind (Tb _) (Vb _) = GT
orderBind (Vb _) (Tb _) = LT
orderBind _ _           = LT  -- PJ 041017: Why not EQ??

{- | Environments associate a set of variables to a variable,
     and types to variables. -}
data Env = Env { env_binds  :: [(Var, Set Var)],
                 env_vtypes :: [(Var, Bind)] } 

empty_env = Env { env_binds = [], env_vtypes = [] }

envLk :: Env -> Var -> Set Var
envLk e x = bindsLk (env_binds e) x

bindsLk :: [(Var, Set Var)] -> Var -> Set Var
bindsLk l x = fromMaybe emptySet (lookup x l)

envConcatBinds :: Env -> [(Var, Set Var)] -> Env
envConcatBinds s l = s { env_binds = (env_binds s) ++ l }

envAddBind :: Bind -> Env -> Env
envAddBind b s = s { env_vtypes = (varOfBind b,b):(env_vtypes s) }

envAddBinds :: [Bind] -> Env -> Env
envAddBinds bs env0 = foldl (flip envAddBind) env0 bs

envTypeOfBind s (Vb (v,t)) = 
    case (fromMaybe (Vb (v,t)) (lookup v (env_vtypes s))) of
    Vb (v,t) -> t
    Tb (v,k) -> error "envTypeOfBind"
envTypeOfBind s (Tb (v,k)) = error "envTypeOfBind"

envBindOfVar :: Env -> Var -> Bind
envBindOfVar s v = case lookup v (env_vtypes s) of
    Just b  -> b
    Nothing -> error ("LambdaLifting.envBindOfVar: " ++ 
		      show v ++ " not found in "++show (env_vtypes s))

-- Parameter lifting

plModule :: Module -> Module
plModule (Module name tdefs vdefgs) = Module name tdefs vdefgs'
    where vdefgs' = foldr filterVdefg [] (map (plVdefg empty_env) vdefgs)
          filterVdefg (Rec []) l = l
          filterVdefg v        l = v:l

{- plVdefg applies plVdef to all subcomponents
   and discards all definitions starting 
   - with "$g" (obfusc. "zdg"): data type foldings and unfoldings
   - or "$W" (obfusc. "zdW")  : newtype foldings
-}
plVdefg :: Env -> Vdefg -> Vdefg
plVdefg s (Rec vdefs) = Rec (foldr plAndFilterVdef [] vdefs)
    where plAndFilterVdef ((_, 'z':'d':c:s),_,_) l | c == 'g' || c == 'W' = l
          plAndFilterVdef vdef l = (plVdef s vdef):l
plVdefg s (Nonrec ((_, 'z':'d':c:st),_,_)) | c == 'g' || c == 'W' = Rec [] 
plVdefg s (Nonrec vdef) = Nonrec (plVdef s vdef)

plVdef :: Env -> Vdef -> Vdef
plVdef s (qvar, ty, exp) = applySolutionToVdef s (qvar, ty, plExp s exp)

plExp :: Env -> Exp -> Exp
plExp s e = case e of 
    Var qvar    -> applySolutionToExp s (Var qvar)
    Dcon qdcon  -> Dcon qdcon
    Lit l       -> Lit l
    App e1 e2   -> App e1' e2'
        where e1' = plExp s e1
              e2' = plExp s e2
    Appt e ty   -> Appt e' ty where e' = plExp s e
    Lam bind e  -> Lam bind (plExp (envAddBind bind s) e)
    Let vdefg e -> Let vdefg' e'
        where (vv, vf) = splitVars vdefg
              funs     = mkSet (map fst vf)
              vfs      = fvMapVdefg vf vdefg 
              g        = foldl add_edges [] vf 
                  where add_edges l (f,b) =
                            let p = setToList 
                                    (intersect funs (bindsLk vfs f))
                                edges = foldl (\ l -> \ h -> (f,f,[h]):l) [] p
                                in edges ++ l
              g'       = stronglyConnCompR g

              succAssoc :: [SCC (Var, Var, [Var])] -> Var -> Set Var
              succAssoc l f = case l of 
                  []                              -> emptySet
                  (AcyclicSCC (g,h,l)):r | f == g -> mkSet l
                  (CyclicSCC l):r                 -> look l
                      where look :: [(Var,Var,[Var])] -> Set Var
                            look []                   = succAssoc r f
                            look ((g,h,l):r) | g == f = mkSet l
                            look (h:r)                = look r
                  h:r                             -> succAssoc r f 
              propagate :: [[Var]] -> [(Var, Set Var)]
              propagate l = case l of
                  []  -> []
                  l:r -> res ++ (propagate r)
                      where res   = map (\f -> (f, minusSet vars (fvars f))) l
                            vars  = union u1 u2
                            u1    = unionManySets (map (bindsLk vfs) l)
                            u2    = unionManySets (map (succAssoc g') l)
                            fvars = \f -> mkSet (fromMaybe [] (lookup f vf))
              redG :: [SCC (Var, Var, [Var])] -> [[Var]]
              redG l = case l of
                  []                     -> []
                  (AcyclicSCC (g,h,l)):r -> [[g]]
                  (CyclicSCC l):r        -> (enumG l):(redG r)
                      where enumG :: [(Var,Var,[Var])] -> [Var]
                            enumG []          = []
                            enumG ((g,h,l):r) = g:(enumG r)
              lf     = redG g'

              s'     = envConcatBinds s vfs
              s''    = envAddBinds (map Vb vv) s'
              vdefg' = plVdefg s'' vdefg
              e'     = plExp s'' e
    Case e vbind alts -> Case e' vbind alts'
         where e'    = plExp s' e
               alts' = map (plAlt s') alts
               s'    = envAddBind (Vb vbind) s
    Coerce ty e     -> Coerce ty e' where e' = plExp s e
    Note str e      -> Note str e' where e' = plExp s e
    External str ty -> External str ty


plAlt :: Env -> Alt -> Alt
plAlt s alt = case alt of 
    (Acon qdc tbs vbs e) -> Acon qdc tbs vbs e' 
        where s' :: Env
              s' = envAddBinds (map Vb vbs) s
              e' = plExp s' e
    (Alit l e)           -> Alit l e'   where e' = plExp s e
    (Adefault e)         -> Adefault e' where e' = plExp s e

applySolutionToVdef :: Env -> Vdef -> Vdef
applySolutionToVdef s ((mName,var), ty, exp@(Lam _b _e)) = res
    where res = ((mName,var), ty', exp')
	  addType t1 (Vb (v,t2)) = funType t2 t1
          addType t1 (Tb (v,k))  = Tforall (v,k) t1
          ty' = foldl addType    ty  lo
          exp'= foldl (flip Lam) exp lo
          lo  :: [Bind]
          lo  = sortBy orderBind (map (envBindOfVar s) lv)
          lv  :: [Var]
          lv  = setToList (envLk s var)
applySolutionToVdef s def = def

applySolutionToExp :: Env -> Exp -> Exp
applySolutionToExp s (Var (mName, v)) = e'
    where e'  = if mName == "" then app else (Var (mName, v))
          app = foldr makeApp (Var (mName, v)) lo
          makeApp b e = 
              case b of
              Vb (v,t) -> App  e (Var (mName, v))
              Tb (v,k) -> Appt e (Tvar v)
          lo :: [Bind]
          lo = sortBy orderBind (map (envBindOfVar s) lv)
          lv :: [Var]
          lv = setToList (envLk s v)
applySolutionToExp s e = e

-- Block floating

bfModule :: Module -> Module 
bfModule (Module name tdefs vdefgs) = Module name tdefs vdefgs'
    where vdefgs' = map bfTopLevelVdefg vdefgs

bfTopLevelVdefg :: Vdefg -> Vdefg
bfTopLevelVdefg (Rec vdefs) = Rec vdefs'
    where vdefs' = unionM (map (\ (v,vl) -> v:vl) (map bfVdef vdefs))
          unionM l = loop [] l
              where loop l []    = l
                    loop l (h:t) = loop (l++h) t
bfTopLevelVdefg (Nonrec vdef) = vdefg
    where vdefg =
              case vl of 
              [] -> Nonrec v
              _   -> Rec (v:vl)
          (v,vl) = bfVdef vdef

bfVdefg :: Vdefg -> (Vdefg, [Vdef])
bfVdefg (Rec vdefs) = (vdefs', vbf) 
    where vdefs'   = case vl of
              []  -> Rec [] 
              [x] -> Nonrec x
              _   -> Rec vl
          (vl, vbf)= foldr bfLam ([], l) vdl
          (vdl, l) = foldr (\ (v,vl) -> \ (l1,l2) -> (v:l1,vl++l2)) ([],[]) r
          r        = map bfVdef vdefs
bfVdefg (Nonrec vdef) = (vdefg, vbf)
    where vdefg = case vl of
                      []  -> Rec [] 
                      [x] -> Nonrec x
                      _   -> error "bfVdefg"
          (vl,vbf)   = bfLam vdef' ([], l) 
          (vdef', l) = bfVdef vdef

bfLam :: Vdef -> ([Vdef],[Vdef]) -> ([Vdef], [Vdef])
bfLam lam (ld, lbf) = 
    case lam of
    ((m,v),ty,Lam b e) ->
        case v of 
--        'p':'r':'o':'p':'z':'u':_     -> (lam:ld, lbf)
--        'l':'e':'m':'m':'a':'z':'u':_ -> (lam:ld, lbf)
        _ -> (ld, ((m,v),ty,Lam b e):lbf)
    e -> (e:ld, lbf)

bfVdef :: Vdef -> (Vdef, [Vdef])
bfVdef (qv,ty,e) = ((qv,ty,e'),l) where (e',l) = bfExp e

bfExp :: Exp -> (Exp, [Vdef])
bfExp e = case e of
    Var qv      -> (Var qv, [])
    Dcon qd     -> (Dcon qd, [])
    Lit l       -> (Lit l, [])
    App e1 e2   -> (App e1' e2', l1++l2) 
        where (e1', l1) = bfExp e1
              (e2', l2) = bfExp e2
    Appt e t    -> (Appt e' t, l) where (e', l) = bfExp e
    Lam b e     -> (Lam b e', l) where (e', l) = bfExp e
    Let vdefg e -> (new_e, l1++l2)
            where new_e = case vdefg' of
                          Rec [] -> e'
                          _      -> Let vdefg' e'
                  (vdefg', l1) = bfVdefg vdefg
                  (e', l2)     = bfExp e
    Case e bind alts -> (Case e' bind alts', l1++l2)
        where (e', l1)    = bfExp e
              (alts', l2) = foldr bfAlt ([],[]) alts
    Coerce ty e   -> (Coerce ty e', l) where (e', l) = bfExp e
    Note s e      -> (Note s e', l)    where (e', l) = bfExp e
    External s ty -> (External s ty, [])

bfAlt :: Alt -> ([Alt],[Vdef]) -> ([Alt],[Vdef]) 
bfAlt a (la, lv) = case a of
    Acon qdcon tbs vbs e -> ((Acon qdcon tbs vbs e'):la, l++lv)
        where (e', l) = bfExp e
    Alit lit e -> ((Alit lit e'):la, l++lv) where (e', l) = bfExp e
    Adefault e -> ((Adefault e'):la, l++lv) where (e', l) = bfExp e

-- Some intermediate functions
-- this ones take a let definition and returns ([var,ty], [(fun, [arg])])
-- var is the list of all names (with types) defined by the let
-- fun is the list of lambda names defined, arg being the bindings made.
type NameDef = ([(Var,Ty)], [(Var, [Var])])

splitVars :: Vdefg -> NameDef
splitVars vdefg = case vdefg of
    Rec vdefs   -> foldl splitVdef ([], []) vdefs
    Nonrec vdef -> splitVdef ([], []) vdef
    
splitVdef :: NameDef -> Vdef -> NameDef
splitVdef (lv,lf) vdef = case vdef of
    ((_,v), ty, e@(Lam _bind _e)) -> ((v,ty):lv, (fbind:lf))
        where fbind = splitExp (v,[]) e
    ((_,v), ty, _)                -> ((v,ty):lv, lf) 

splitExp :: (Var, [Var]) -> Exp -> (Var, [Var])
splitExp (f,larg) e = case e of
    Lam bind e -> splitExp (f,(varOfBind bind):larg) e
    _          -> (f,larg)

{- | Free variables. This probably contains a bug, I always make a bug
     in those things. -}

fvMapVdefg :: [(Var, [Var])] -> Vdefg -> [(Var, Set Var)]
fvMapVdefg fv vdefg = case vdefg of
    Rec vdefs   -> foldl (findFv fv) [] vdefs
    Nonrec vdef -> findFv fv [] vdef

findFv :: [(Var, [Var])] -> [(Var, Set Var)] -> Vdef -> [(Var, Set Var)]
findFv fv l ((mName, v), ty, e) = l'
    where l' = case lookup v fv of
              Nothing -> l
              Just _  -> fvv:l
          fvv = (v, fvExp (fvEmptyEnv mName v) e)

data FvEnv = FE { bound   :: Set Var, 
                  free    :: Set Var,
                  modName :: String }

fvEmptyEnv :: String -> Var -> FvEnv
fvEmptyEnv mName fName = FE { bound   = mkSet [fName], 
                              free    = emptySet,
                              modName = mName }

returnFree :: FvEnv -> Set Var
returnFree fe = free fe

fvBind :: FvEnv -> Bind -> FvEnv
fvBind fe (Vb (v,t)) = fe { bound = addToSet (bound fe) v }
fvBind fe (Tb (v,k)) = fe { bound = addToSet (bound fe) v }

fvCheckBind :: FvEnv -> Qual Var -> Set Var
fvCheckBind fe (mName, vName) = returnFree fe'
    where fe'     = if isFree then fe { free = addToSet (free fe) vName }
                              else fe
          isFree  = isLocal && (not (elementOf vName (bound fe)))
          isLocal = mName == (modName fe)

fvBindVdef :: FvEnv -> Vdef -> FvEnv
fvBindVdef fe ((mName, vName), ty, e) = fvBind fe (Vb (vName, ty))

fvVdefg :: FvEnv -> Vdefg -> FvEnv
fvVdefg fe (Rec vdefs)   = foldl fvVdef (foldl fvBindVdef fe vdefs) vdefs
fvVdefg fe (Nonrec vdef) = fvVdef (fvBindVdef fe vdef) vdef

fvVdef :: FvEnv -> Vdef -> FvEnv
fvVdef fe ((mName, vName), ty, e) = fe { free = fvExp fe e } 

fvExp :: FvEnv -> Exp -> Set Var
fvExp fe e = case e of 
    Var qvar    -> fvCheckBind fe qvar
    Dcon dcon   -> returnFree fe
    Lit l       -> returnFree fe
    App e1 e2   -> fv 
        where fv  = union fv1 fv2
              fv1 = fvExp fe e1
              fv2 = fvExp fe e2
    Appt e t    -> fv 
        where fv = union fv1 fv2 
              fv1 = fvExp fe e
              fv2 = fvTy fe t
    Lam bind e  -> fvExp (fvBind fe bind) e
    Let vdefg e -> fv 
        where fv  = fvExp fel e 
              fel = fvVdefg fe vdefg
    Case e (var,ty) alts -> unionManySets (fve:fty:fel)
        where fel = map (fvAlt (fvBind fe (Vb (var, ty)))) alts
              fty = fvTy fe ty
              fve = fvExp fe e
    Coerce ty e -> fvExp fe e
    Note str e  -> fvExp fe e
    External str ty -> returnFree fe

fvAlt :: FvEnv -> Alt -> Set Var
fvAlt fe alt = case alt of
    Acon qdcon tbinds vbinds e -> fv
        where fv  = fvExp fb e 
              fb  = foldl (\fe -> \b -> fvBind fe (Vb b)) ft vbinds
              ft  = foldl (\fe -> \b -> fvBind fe (Tb b)) fe tbinds
    Alit l e   -> fvExp fe e
    Adefault e -> fvExp fe e

fvTy :: FvEnv -> Ty -> Set Var
fvTy fe ty = case ty of
    Tvar var         -> fvCheckBind fe ("", var)
    Tcon qtcon       -> fvCheckBind fe qtcon
    Tapp ty1 ty2     -> fv 
        where fv  = union fv1 fv2
              fv1 = fvTy fe ty1
              fv2 = fvTy fe ty2
    Tforall tbind ty -> fvTy (fvBind fe (Tb tbind)) ty

{-| Naming anonymous functions

    The renaming is done in a state monad. The state is of type
    @(String, Int)@. The string is the name of the toplevel definition
    currently visited, the integer a symbol generator. From a state
    @(f,i)@, we generate a name @f ++ "_" ++ (show i)@. -}

genName :: () -> State (String, Int) (Qual Var)
genName () = do (f,i) <- get
		let name = f ++ "_" ++ (show i)
		put (f,i+1)
		return ("", name)

nameModule :: Module -> Module
nameModule (Module name tdefs vdefgs) = (Module name tdefs vdefgs')
     where vdefgs' = map nTopLevelVdefg vdefgs

nTopLevelVdefg :: Vdefg -> Vdefg
nTopLevelVdefg vdefg = 
    case vdefg of 
    Rec vs   -> Rec (map nTopLevelVdef vs)
    Nonrec v -> Nonrec (nTopLevelVdef v)

nTopLevelVdef :: Vdef -> Vdef 
nTopLevelVdef ((m,v),t,e) = ((m,v), t, a)
    where a = evalState (nTopLevelExp e) (v,0)

{- The following functions have as state a pair 
(current function name :: String, gensym index :: Int) -}

nTopLevelExp :: Exp -> State (String, Int) Exp
nTopLevelExp e = 
    case e of 
    Lam b e  -> do a <- nTopLevelExp e; return (Lam b a)
    Note s e -> do a <- nTopLevelExp e; return (Note s a)
    _        -> nExp e

nVdefg :: Vdefg -> State (String, Int) Vdefg
nVdefg vdefg = 
    case vdefg of
    Rec vs   -> do a <- mapM nVdef vs; return (Rec a)
    Nonrec v -> do a <- nVdef v; return (Nonrec a)

nVdef :: Vdef -> State  (String, Int) Vdef
nVdef ((m,v),t,e) = do a <- nExp e; return ((m,v),t,a)

-- \ v:t. e1, e2 becomes let name : t -> (typeOf e1) = \ v:t. e1 in e2
buildDef :: Qual Var -> Var -> Ty -> Exp -> Exp -> Exp
buildDef name v t e1 e2 = 
    Let (Nonrec (name, (funType t (fst (typeExp [] e1))),
		 (Lam (Vb (v,t)) e1))) e2

nExp :: Exp -> State (String, Int) Exp
nExp e = 
    case e of 
    Var q              -> return (Var q) 
    Dcon q             -> return (Dcon q) 
    Lit l              -> return (Lit l) 
    App (Lam (Vb (v,t)) e1) e2 ->
        do a <- nExp e1
	   b <- nExp e2 
	   name <- genName ()
	   let app = App (Var name) b
	   return (buildDef name v t a app)
    -- For now, we don't want to lift the argument of a forAll or an
    -- exists.
    -- Moreover, we don't want to lift the lambda in: $ (forAll, \x.e)
    -- (same for exists)
    -- In the long term, we'll want to have an evaluator
    -- (those specials might be kept anyway to avoid lifting, then inlining).
    App (Appt (Var ("Property", "forAll")) t) (Lam b c) -> 
        do a <- nExp c
           return (App (Appt (Var ("Property", "forAll")) t) (Lam b a))
    App (Appt (Var ("Property", "exists")) t) (Lam b c) -> 
        do a <- nExp c
           return (App (Appt (Var ("Property", "exists")) t) (Lam b a))
    App (App (Appt (Appt (Var ("GHCziBase", "zd")) t1) t2) 
	 (Appt (Var ("Property", "forAll")) t3)) (Lam b c) ->
        do a <- nExp c
	   return (App (Appt (Var ("Property", "forAll")) t3) (Lam b a))
    App (App (Appt (Appt (Var ("GHCziBase", "zd")) t1) t2) 
	 (Appt (Var ("Property", "exists")) t3)) (Lam b c) ->
        do a <- nExp c
	   return (App (Appt (Var ("Property", "exists")) t3) (Lam b a))
    -- -----
    App e1 e2          -> liftM2 App (nExp e1) (nExp e2)
    Appt e t           -> do a <- nExp e; return (Appt a t)
    Lam b e            ->
        do a <- nTopLevelExp e
	   name <- genName ()
	   let t = case b of 
		   Vb (v,t) -> funType t     (fst (typeExp [] a))
		   Tb (v,k) -> Tforall (v,k) (fst (typeExp [] a))
           return (Let (Nonrec (name, t, Lam b a)) (Var name))
    Let v e            -> liftM2 Let (nVdefg v) (nExp e)
    Case e b als       -> do a <- nExp e
                             c <- mapM nAlt als
                             return (Case a b c)
    Coerce t e         -> liftM (Coerce t) (nExp e)
    Note s e           -> liftM (Note s)   (nExp e)
    External s t       -> return (External s t)

nAlt :: Alt -> State (String, Int) Alt
nAlt a = case a of
    Acon q ts vs e -> do a <- nExp e; return (Acon q ts vs a)
    Alit l e       -> do a <- nExp e; return (Alit l a)
    Adefault e     -> do a <- nExp e; return (Adefault a)

-- Putting types back
-- This part needs serious work. (Roughly, we want a type inference algorithm)

instance Eq Ty where
    (==) (Tvar v1) (Tvar v2) = (v1 == v2)
    (==) (Tcon c1) (Tcon c2) = (c1 == c2)
    (==) _ _                 = False
--    (==) (Tapp t1 t2) (Tapp t1' t2') = (t1 == t1') && (t2 == t2')

--tWild = error "LambdaLifting.tWild: unknown type"
--tWild = observe "hej" $ Tvar "?"
tWild = Tvar "?"

{- type environment: a finite mapping from ids (strings) to types -}
type TEnv = [(String,Ty)]

tLk :: TEnv -> Qual Tcon -> Ty
tLk env (mName, var) =
    case mName of 
    "" -> fromMaybe tWild (lookup var env) 
    "DataziTuple" -> 
        case var of
        "Z2T" -> Tcon ("", "Pair")
    _ -> tWild

{- 'supType t1 t2': computes the information-theoretic supremum of the
two passed types, where '?' means no information. -}

supType :: Ty -> Ty -> Ty
supType (Tvar "?") t                = t
supType t (Tvar "?")                = t
supType (Tapp t1 t2) (Tapp t1' t2') = Tapp (supType t1 t1') (supType t2 t2')
supType t1 t2 | t1 == t2            = t1
              | otherwise           = t1
-- **PJ: why is supType t1 t2 always t1, but still written as two cases?

typeModule :: Module -> Module
typeModule (Module name tdefs vdefgs) = (Module name tdefs vdefgs')
    where vdefgs' = map (\v -> snd (typeVdefg [] v)) vdefgs
 
typeVdefg :: TEnv -> Vdefg -> (TEnv, Vdefg)
typeVdefg env vdefg = case vdefg of
    Rec vs   -> (env', Rec vs') 
        where (env', vs')       = foldr loopVdef (env, []) vs
              loopVdef v (e,vs) = (e',v':vs) where (e',v') = typeVdef e v 
    Nonrec v -> (env', Nonrec v') where (env', v') = typeVdef env v

typeVdef :: TEnv -> Vdef -> (TEnv, Vdef)
typeVdef env ((mName, v), t, e) = (env', ((mName, v), nt, e'))
    where env'    = (v,nt):env
          nt      = supType t t'
          (t',e') = typeExp ((v,t):env) e

typeExp :: TEnv -> Exp -> (Ty, Exp)
typeExp env e = case e of 
    Var qv    -> (tLk env qv, e)
    Dcon qd   -> (tLk env qd, e)
    Lit l     -> (typeLit l, e)
    App e1 e2 -> (tApp, App e1' e2')
        where (t1, e1') = typeExp env e1
              (t2, e2') = typeExp env e2
              tApp      = case t1 of 
                  Tapp(Tapp(Tcon arr) targ) tres | (arr == tcArrow) -> tres
                  Tforall tb ty -> ty
                  _ -> t1
    Appt e1 t -> (tApp, Appt e1' t)
        where (te, e1') = typeExp env e1
              tApp      = Tapp te t
    Lam (Vb (v,t)) e1 -> (tLam, Lam (Vb (v,t')) e')
        where t'      = supType t (fromMaybe tWild (lookup v env))
              (te,e') = typeExp ((v,t'):env) e1
              tLam    = Tapp(Tapp(Tcon tcArrow) t') te
    Lam (Tb tb) e1 -> (tLam, Lam (Tb tb) e')
        where (te,e') = typeExp env e1
              tLam    = Tforall tb te
    Let vdefg e1 -> (te, Let vdefg' e')
        where (te, e')       = typeExp env' e1
              (env', vdefg') = typeVdefg env vdefg
    Case e1 (v,t) alts -> (tc, Case e' (v,t'') alts')
        where (tc, alts') = typeAlts ((v,t'):env) alts
              t'' = supType (supType (fromMaybe tWild (lookup v env)) t) t'
              (t', e')    = typeExp env e1
    Coerce t e1  -> (t, Coerce t e') where (t', e') = typeExp env e1
    Note s e1    -> (t, Note s e')   where (t, e') = typeExp env e1
    External s t -> (t, External s t)
  
typeAlts :: TEnv -> [Alt] -> (Ty, [Alt])
typeAlts env as = (t, as')
    where (t, as') = foldr (\ (t2,a) (t1,as) -> (supType t1 t2, a:as)) 
                           (tWild, []) tas 
          tas      = map (tAlt env) as
          tAlt env alt = case alt of 
              Acon qd tb vb e -> (t, Acon qd tb vb e')
                  where (t,e') = typeExp (vb ++ env) e
              Alit l e        -> (t, Alit l e')   where (t,e') = typeExp env e
              Adefault e      -> (t, Adefault e') where (t,e') = typeExp env e 

typeLit :: Lit -> Ty
typeLit lit = case lit of 
    Lint      _ t -> t
    Lrational _ t -> t
    Lchar     _ t -> t
    Lstring   _ t -> t
