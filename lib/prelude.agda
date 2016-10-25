-- BEGIN prelude.agda

-- the Haskell $ and .

($) (A::Set) (B::Set) (f :: A -> B) (a :: A) :: B
  = f a

compose (B,C,A::Set)(f :: B -> C)(g :: A -> B) :: A -> C
  = \ (x::A) -> f (g x)

{- hardwired into Agda

Integer :: Set
  = ?

Bool :: Set
  = data True | False

-}

not (b::Bool) :: Bool
  = case b of {
      (True) -> False;  -- Agda does not require @_ for built-in constructors
      (False) -> True;}

(||) (b1::Bool)(b2::Bool) :: Bool
  = case b1 of {
      (True) -> True@_;
      (False) ->
        case b2 of {
          (True) -> True@_;
          (False) -> False@_;};}

(&&) (b1::Bool)(b2::Bool) :: Bool
  = case b1 of {
      (True) ->
        case b2 of {
          (True) -> False@_;
          (False) -> True@_;};
      (False) -> False@_;}

Pair (a::Set)(b::Set) :: Set
  = data Pair (x::a) (y::b)

Triple (a::Set)(b::Set)(c::Set) :: Set
  = data Triple (x::a) (y::b) (z::c)

flip (a::Set)(b::Set)(c::Set)(f::a -> b -> c)(x::b)(y::a) :: c
  = f y x

{- hardwired into Agda:

List (a::Set) :: Set
  = data Nil | (:) (x::a) (xs::List a)

-}

foldl (a::Set)(b::Set)(f::a -> b -> a)(acc::a)(l::List b) :: a
  = case l of {
      (Nil) -> acc;
      (x:xs) -> foldl a b f (f acc x) xs;}

reverse (a::Set)(l::List a) :: List a
  = foldl (List a) a
      (flip a (List a) (List a) (\(h::a) -> \(h'::List a) -> (:)@_ h h'))
      Nil@_
      l

append (a::Set)(l1::List a)(l2::List a) :: List a
  = case l1 of {
      (Nil) -> l2;
      (x:xs) -> x : (append a xs l2);}

null (a::Set)(l::List a) :: Bool
  = case l of {
      (Nil) -> True@_;
      (x:xs) -> False@_;}

map (a,b::Set)(f::a -> b)(l::List a) :: List b
  = case l of 
       (Nil)  -> Nil
       (x:xs) -> f x : map a b f xs

Maybe (a::Set) :: Set
  = data Nothing | Just (x::a)

-- Should not be here - temporary addition to provide an "interesting" type
-- data Simple = A | B | C  -gone


-- Properties
-- naive implementation of Property.hs


-- from SET.alfa
Rel (X::Set) :: Type
  = X -> X -> Set
Id (X::Set) :: Rel X
  = idata ref (x::X) :: _ x x
Zero :: Set
  = data 
whenZero (X::Set)(z::Zero) :: X
  = case z of { }
Unit :: Set
  = data tt
Sum (X::Set)(Y::X -> Set) :: Set
  = sig{fst :: X;
        snd :: Y fst;}
Plus (X::Set)(Y::Set) :: Set
  = data inl (x::X) | inr (y::Y)

package Property where

  Prop :: Type 
    = Set

  (===) (A :: Set) (a :: A) (b :: A) :: Prop
    = Id A a b
  
  -- translate forAll into a dependent function type
  forAll (A :: Set) (f :: A -> Prop) :: Prop
    = (x :: A) -> f x
  
  exists (A :: Set) (f :: A -> Prop) :: Prop
    = sig { witness :: A; 
            prop    :: f witness; }
  
  (/\) (A,B :: Prop) :: Prop
    = Sum A (\(a::A) -> B)
  
  (\/) (A,B :: Prop) :: Prop
    = Plus A B
  
  (<=>) (A,B :: Prop) :: Prop
    =  (A -> B) /\ (B -> A)
  
  (==>) (A,B :: Prop) :: Prop
    =  (A -> B)
  
  true :: Prop
    = Unit
  
  false :: Prop
    = Zero
  
  nt (A :: Prop) :: Prop
    =  A -> false
  
  -- cannot do the naive using because of universe conflict
  -- List cannot have a parameter which is not a set, and Prop is a type
  --using (L :: List Prop) (A :: Prop) :: Prop
  --  = A
  
  holds (b::Bool) :: Prop
    = if b then true else false
  
  holdsNot (b::Bool) :: Prop
    = if b then false else true
  
-- Class of inhabited types

class Inhabited (a::Set) :: Set exports
  arbitrary :: a

error (a::Set)(|ia::Inhabited a)(msg::String) :: a
  = arbitrary

-- Prelude types are inhabited

instance iBool :: Inhabited Bool where
  arbitrary = True

instance iString :: Inhabited String where
  arbitrary = "I AM ARBITRARY"

instance iInteger :: Inhabited Integer where
  arbitrary = 123456789

{- Syntax error:
instance iRational :: Inhabited Rational where
  arbitrary = 0.123456789
-}

instance iList (|a::Set) :: Inhabited (List a) where
  arbitrary = Nil
-- instance iList (a::Set)(ia::Inhabited a)  :: Inhabited (List a) where


-- END prelude.agda
