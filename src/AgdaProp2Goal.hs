{- AgdaProp2Goal.hs

Author     : Andreas Abel
Created    : Nov 15, 2004
Description: 

Traverses an Agda module and adds to every 

  prop_<id> :: <Tel> -> Prop
            = e

a new definition

  goal_<id> :: Prop
            = Pi <Tel> -> e

This applies only to top-level definitions and definitions in
top-level packages, but not to local let!  -}

module AgdaProp2Goal (agdaProp2Goal) where

import AbsAlfa
import Core2Agda(aIdent)

--- Boilerplate code -------------------------------------------------

agdaProp2Goal :: Module -> Module
agdaProp2Goal (Module decls) = Module (decls2decls decls)

-- 'decls2decls' used also for 'body2body'
decls2decls :: [Decl] -> [Decl]
decls2decls = foldr (\d ds -> decl2decls d ++ ds) []
               
decl2decls :: Decl -> [Decl]
decl2decls (DDef attrs def) = map (DDef attrs) (def2defs def)
decl2decls (DImp imp) = [DImp imp] -- import

def2defs :: Def -> [Def]
def2defs (Value x delta a e) = valueDef2defs x delta a e -- x(Delta) :: a = t
def2defs (Package x typings body) = [Package x typings (body2body body)]
def2defs (Mutual defs) = [Mutual (foldr (\d ds -> def2defs d ++ ds) [] defs)]
def2defs def = [def]

-- the package body might also contain prop_<id>s
body2body :: PackageBody -> PackageBody
body2body (PackageDef decls) = PackageDef (decls2decls decls)
body2body (PackageInst exp)  = PackageInst exp

--- Interesting code -------------------------------------------------

valueDef2defs :: AIdent -> [VarDecl] -> Exp -> Exp -> [Def]
valueDef2defs aid@(F (PIdent (_, x))) delta a e = 
    [Value aid delta a e] ++
    if prefix /= "prop_" then []
    else case predToTel dummies a of
         Nothing -> []
         Just delta' -> [Value (aIdent ("goal_"++suffix)) [] EType
                         (quantify (delta++delta') (EVar aid))]

    where (prefix, suffix) = splitAt 5 x

-- expProp :: Exp 
-- expProp = EVar (aIdent "Property.Prop")

dummies :: [AIdent]
dummies = map (aIdent . ("xGoal" ++) . show) [1..]

{- @predToTel e@ checks whether e is of the form 
@
  (xs::As) -> Property.Prop
@
If yes, it returns the list (xs::As), otherwise nothing -}

predToTel :: [AIdent] -> Exp -> Maybe [VarDecl]
predToTel fresh (EPi vdecl hide e) = 
    do delta <- predToTel fresh e
       return $ updateHiding hide vdecl : delta
predToTel (x:xs) (EFun a hide e) =
    do delta <- predToTel xs e
       return $ (VDecl [bound hide x] a) : delta
predToTel fresh (EVar (F (PIdent (_, "Property.Prop")))) = return []
predToTel fresh e = Nothing

{- @quantify (xs::As) e = (xs::As) -> e xs@ -}

quantify :: [VarDecl] -> Exp -> Exp

quantify [] e = e

{- The Agda parser is a bit inconsequent: (|x::A) -> B is rejected,
instead of being accepted as a synonym for (x::A) |-> B. 
Therefore we need a special case: -}
quantify (VDecl bs@[BHide id] a : delta) e = 
    EPi (VDecl [BVar id] a) AHide (quantify delta (e `apply` bs))

quantify (vdecl@(VDecl bs a) : delta) e = 
    EPi vdecl AShow (quantify delta (e `apply` bs))

{- @apply e bs = e bs@ -}
apply :: Exp -> [Bound] -> Exp
e `apply` []              = e
e `apply` (BVar  id : bs) = (e `EApp`    (EVar id)) `apply` bs
e `apply` (BHide id : bs) = (e `EAppHid` (EVar id)) `apply` bs

--- Auxiliary functions for hiding -----------------------------------

{- updateHiding tries to make sense of 

  (|a,b :: A) |->

and similar ambiguities.  The semantics is not clear.  We assume that

  (as :: A) |->

means

  (|as :: A) ->

-}

updateHiding :: Arrow -> VarDecl -> VarDecl
updateHiding AShow vdecl = vdecl
updateHiding AHide (VDecl bs a) = VDecl (map hide bs) a

hide :: Bound -> Bound
hide (BVar  id) = BHide id
hide (BHide id) = BHide id

bound :: Arrow -> AIdent -> Bound
bound AShow = BVar
bound AHide = BHide

-- EOF
