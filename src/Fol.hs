module Fol where

data Id = Qname String String
 deriving (Eq,Ord,Show)

data Term =
   Fvar Id
 | Ffun Id 
 | Fcon Id
 | Fapp Term Term
 deriving (Eq,Ord,Show)

data ClBody = ClEqual Term Term

data Clause =
   Cl    ClBody
 | ClNot ClBody
 | ClOr [Clause]
 | ClInline Id
 | ClNinline Id

type Def      = (Id, Clause)
type Prop     = (Id,[Id],[Clause],[Clause])
--   ProofObl = name, program clauses, proposition clauses
type ProofObl = (Id,[Clause],[Clause])

--   Library  = name, allow lookup in defs?, definitions, properties
type Library  = (String, Bool, [Fol.Def], [Fol.Prop])

{- Finding all the function names used in a term, body, or clause -}
fvTerm :: Id -> [Id] -> Term -> [Id]
fvTerm self fv t = 
    case t of 
    Fvar _     -> fv
    Ffun s     -> if (elem s fv) || (s == self) then fv else s:fv
    Fcon _     -> fv
    Fapp t1 t2 -> fvTerm self (fvTerm self fv t1) t2

fvClBody :: Id -> [Id] -> ClBody -> [Id]
fvClBody self fv (ClEqual t1 t2) = fvTerm self (fvTerm self fv t1) t2

fvClause :: Id -> [Id] -> Clause -> [Id]
fvClause self fv c = 
    case c of
    Cl b         -> fvClBody self fv b
    ClNot b      -> fvClBody self fv b
    ClOr lc      -> foldl (fvClause self) fv lc
    ClInline id  -> fv
    ClNinline id -> fv
