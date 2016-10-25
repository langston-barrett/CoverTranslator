{-# OPTIONS -fglasgow-exts #-}
module Property
  -- abstract type of properties
  ( Prop   
  
  -- equality
  , (===)
  
  -- property building functions
  , forAll
  , exists
  , (/\)
  , (\/)
  , (<=>)
  , (==>)
  , true
  , false
  , nt

  , using

  -- derived
  , holds
  , holdsNot
  )
 where

import qualified Debug.QuickCheck as Q

--------------------------------------------------------------------------
-- fixeties

infix  5 ===
infixr 4 <=>
infixr 3 /\
infixr 2 \/
infixr 1 ==>

type Prop = Bool

using _ = id
true	= True
false	= False
nt	= not
x === y	= Q.property $ x == y

x ==> y	= nt y \/ x

holdsNot    = nt
holds	    = id

forAll f    = Q.forAll Q.arbitrary f

exists	= error "Cannot quickCheck exists!"

(\/)	= (||)
(/\)	= (&&)
x <=> y	= (x ==> y) /\ (y ==> x)

