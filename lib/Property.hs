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

--------------------------------------------------------------------------
-- fixeties

infix  5 ===
infixr 4 <=>
infixr 3 /\
infixr 2 \/
infixr 1 ==>

--------------------------------------------------------------------------
-- Prop

-- here, we have to pick a subset of property operations:
--
-- * not too many (otherwise it is cumbersome to write functions
--     that process properties)
--
-- * not too few (we still want to able to express everything we
--     want to be able to express, without the size of the formulas
--     exploding)

data Prop
  = forall a . ForAll (a -> Prop)    -- these should later be annotated
  | forall a . Exists (a -> Prop)    -- with sets
  | And   Prop Prop
  | Or    Prop Prop
  | Equiv Prop Prop
  | Not   Prop
  | Bool  Bool
  | forall a . Equal a a
  | Using [Prop] Prop

-- issues:
--
-- * 'Or' could be expressed in terms of 'And' with the help of 'Not'.
--   'Exists' could be expressed in terms of 'ForAll'. 'false' in terms
--   of 'true', etc. Seems an artificial simplification?
--

--------------------------------------------------------------------------
-- primitives

forAll, exists :: (a -> Prop) -> Prop
forAll = ForAll
exists = Exists

(/\), (\/), (<=>) :: Prop -> Prop -> Prop
(/\)  = And
(\/)  = Or
(<=>) = Equiv

nt :: Prop -> Prop
nt = Not
{- alternative:
nt (Not p) = p
nt p       = Not p
-}

false, true :: Prop
false = Bool False
true  = Bool True

(===) :: a -> a -> Prop
(===) = Equal

using :: [Prop] -> Prop -> Prop
using = Using

--------------------------------------------------------------------------
-- derived

(==>) :: Prop -> Prop -> Prop
p ==> q = nt p \/ q

holds :: Bool -> Prop
holds b = b === True

holdsNot :: Bool -> Prop
holdsNot b = b === False

--------------------------------------------------------------------------
-- the end.


