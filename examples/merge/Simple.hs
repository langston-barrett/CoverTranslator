module Simple where

-- data Simple = A | B | C deriving (Eq, Ord)

data Simple = A | B | C

{-
instance Eq Simple where
  A == A  = True
  B == B  = True
  C == C  = True
  _ == _  = False

instance Ord Simple where
  B <= A  = False
  C <= A  = False
  C <= B  = False
  _ <= _  = True
-}

less  B A  = False
less  C A  = False
less  C B  = False
less  _ _  = True
{-
less  A B  = True
less  A C  = True
less  B C  = True
less  A A  = True
less  B B  = True
less  C C  = True
-}

