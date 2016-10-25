module CaseAbstraction where

import ExternalCore(Module(Module),Exp(App, Appt, Case, Coerce, Dcon, 
  External, Lam, Let, Lit, Note, Var),Alt(Acon, Adefault, Alit),
  Module, Vdefg(Nonrec, Rec), Ty(Tapp, Tcon, Tforall, Tvar), Bind(Vb))

data KeepKind = AllTopLevel | VarTopLevel
                deriving Eq

-- | Case abstraction transforms Case of expression to case of variable

caseAbstract :: KeepKind -> Module -> Module
caseAbstract k (Module name tdefs vdefgs) = (Module name tdefs vdefgs')
    where vdefgs' = map (caTopLevelVdefg k) vdefgs

caTopLevelVdefg k (Rec vs)   = Rec (map (caTopLevelVdef k) vs)
caTopLevelVdefg k (Nonrec v) = Nonrec (caTopLevelVdef k v)

caTopLevelVdef k (q,t,e) = (q,t,caTopLevelExp k e)

caTopLevelExp k e = case e of
    Lam b e                    -> Lam b (caTopLevelExp k e)
    Case vb@(Var (_m,x)) (z,ty) bs -> Case vb (x,ty) bs'
        where bs' = map (\a -> caAlt caTopLevelExp k (substAlt (z,x) a)) bs
    Case vb (z,ty) bs 
        | k == AllTopLevel     -> Case vb (z,ty) bs'
        where bs' = map (\a -> caAlt caTopLevelExp k a) bs
    e                          -> caExp k e

caVdefg k (Rec vs)   = Rec (map (caVdef k) vs)
caVdefg k (Nonrec v) = Nonrec (caVdef k v)

caVdef k (q,t,e) = (q,t,caExp k e)

caExp k e = case e of
    Var q        -> Var q
    Dcon q       -> Dcon q
    Lit l        -> Lit l
    App e1 e2    -> App (caExp k e1) (caExp k e2)
    Appt e1 t    -> Appt (caExp k e1) t
    Lam b e      -> Lam b (caTopLevelExp k e)
    Let v e      -> Let (caVdefg k v) (caExp k e)
    Case e b bs  -> App 
                      (Lam (Vb b) 
                       (Case (Var ("", (fst b))) b (map (caAlt caExp k) bs))) 
                      (caExp k e)
    Coerce t e   -> Coerce t (caExp k e)
    Note s e     -> Note s (caExp k e)
    External s t -> External s t

caAlt fun k a = case a of
    Acon q ts vs e -> Acon q ts vs (fun k e)
    Alit l e       -> Alit l (fun k e)
    Adefault e     -> Adefault (fun k e)

-- Substitution 
-- No name clash should occur: no check is done!

substVdefg (x,z) d = case  d of
    Rec vdl   -> Rec (map (substVdef (x,z)) vdl)
    Nonrec vd -> Nonrec (substVdef (x,z) vd)

substVdef (x,z) ((m,v), ty, e) = ((m,v), substTy (x,z) ty, substExp (x,z) e)

substExp (x,z) e = case e of
    Var ("", v)      -> Var ("", if v == x then z else v)
    App e1 e2        -> App (substExp (x,z) e1) (substExp (x,z) e2)
    Appt e t         -> Appt (substExp (x,z) e) (substTy (x,z) t)
    Lam b e          -> Lam b (substExp (x,z) e)
    Let vdefg e      -> Let (substVdefg (x,z) vdefg) (substExp (x,z) e)
    Case e bind alts -> Case (substExp (x,z) e) bind alts'
        where alts' = map (substAlt (x,z)) alts
    Coerce ty e      -> Coerce (substTy (x,z) ty) (substExp (x,z) e)
    Note s e         -> Note s (substExp (x,z) e)
    External s ty    -> External s (substTy (x,z) ty)
    _                -> e

substAlt (x,z) a = case a of
    Acon c tb vb e -> Acon c tb' vb' e'
        where tb' = map (substTbind (x,z)) tb
              vb' = map (substVbind (x,z)) vb
              e'  = substExp (x,z) e
    Alit l e       -> Alit l (substExp (x,z) e)
    Adefault e     -> Adefault (substExp (x,z) e)

substVbind (x,z) (v,ty) = (v',ty') 
    where v'  = if v == x then z else v
          ty' = substTy (x,z) ty

substTbind (x,z) (v,k) = (if v == x then z else v, k)

substTy (x,z) ty = case ty of
    Tvar v        -> Tvar (if v == x then z else v)
    Tcon qt       -> Tcon qt
    Tapp ty1 ty2  -> Tapp (substTy (x,z) ty1) (substTy (x,z) ty2)
    Tforall tb ty -> Tforall (substTbind (x,z) tb) (substTy (x,z) ty)
