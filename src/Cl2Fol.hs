module Cl2Fol(cl2fol) where

import Cl.Abs as Cl
import Fol

import Maybe

cl2fol :: Cl.Module -> ([Fol.Def],[Fol.Prop])
cl2fol (Cl.Mod code prop) = (map c2f code, map p2f prop)

c2f :: Cl.Clause -> Fol.Def
c2f (Cl.Cl id ps gs e ls) = (c2fId id,folClause)
    where folClause = case (defGuard, defLocal) of
                      ([], []) -> defClause
                      (_, _) -> ClOr (defClause:defGuard++defLocal)
          defClause = Fol.Cl (ClEqual (c2fDecl id ps) (c2fExp e))
          defGuard  = map c2fGuard gs
          defLocal  = map c2fLocal ls

c2fGuard :: Cl.Guard -> Fol.Clause
c2fGuard (Guard es) = 
    ClOr (map (\ e -> ClNot (ClEqual (c2fExp e) (Fcon (Fol.Qname "" "true")))) es)

c2fLocal :: Cl.Local -> Fol.Clause
c2fLocal (Loc ds) = ClOr (map c2fDef ds)

-- PJ+KC: negated because only use is in c2fLocal
c2fDef :: Cl.Def -> Fol.Clause
c2fDef (Def p e) = Fol.ClNot (ClEqual (c2fPat p) (c2fExp e))

c2fExp :: Cl.Exp -> Fol.Term
c2fExp e = case e of
    Evar id    -> Fvar (c2fId id)
    Efun id    -> Ffun (c2fId id)
    Econ id    -> Fcon (c2fId id)
    Eapp e1 e2 -> Fapp (c2fExp e1) (c2fExp e2)

c2fPat :: Cl.Pat -> Fol.Term
c2fPat p = case p of
    Pvar id    -> Fvar (c2fId id)
    Pcon id ps -> foldl (\ t -> \ p -> Fapp t (c2fPat p)) (Fcon (c2fId id)) ps

c2fDecl :: Cl.Id -> [Cl.Pat] -> Fol.Term
c2fDecl id ps = foldl (\ t -> \ p -> Fapp t (c2fPat p)) (Ffun (c2fId id)) ps

c2fId :: Cl.Id -> Fol.Id
c2fId (Cl.Qname (Ident m) (Ident v)) = Fol.Qname m v

p2f :: Cl.PropCl -> Fol.Prop
p2f (Property v l pt pf) = (c2fId v, map c2fId l, map p2fCl pt, map p2fCl pf)

p2fCl :: Cl.Pcl -> Fol.Clause
p2fCl (PCl l) = Fol.ClOr (map p2fLit l)

p2fLit :: Cl.Lit -> Fol.Clause
p2fLit (Lpos e1 e2) = Fol.Cl    (ClEqual (c2fExp e1) (c2fExp e2))
p2fLit (Lneg e1 e2) = Fol.ClNot (ClEqual (c2fExp e1) (c2fExp e2))
p2fLit (Linline id) = Fol.ClInline (c2fId id)
p2fLit (Lninline id) = Fol.ClNinline (c2fId id)
