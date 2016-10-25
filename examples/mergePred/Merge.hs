module Merge where
import Property
import PredPrelude
import Simple

-- The program

merge []     ys     = ys
merge xs     []     = xs
merge (x:xs) (y:ys)  
  | less x y        = x : merge xs (y:ys)
  | otherwise       = y : merge (x:xs) ys

mergesweep []          = []
mergesweep [xs]        = [xs]
mergesweep (xs:ys:xss) = merge xs ys : mergesweep xss

merging []   = []
merging [xs] = xs
merging xss  = merging (mergesweep xss)

--msort xs = merging [ [x] | x <- xs ]
msort xs = merging (unitify xs)

-- Make it non-polymorphic
unitify :: [Simple] -> [[Simple]]
unitify []     = []
unitify (x:xs) = [x] : unitify xs

-- The properties

{-
newtype OrderedList a = Ordered [a]

-- lowerBound :: Ord a => a -> OrderedList a -> Prop
lowerBound a (Ordered [])     = true
lowerBound a (Ordered (x:xs)) = holds (less a x) 

-- ordered :: Ord a => [a] -> Prop
ordered []           = true
ordered (x:xs)       = lowerBound x (Ordered xs) /\ ordered xs

prop_merge_lowerBound a xs ys =
  lowerBound a xs ==> lowerBound a ys ==> lowerBound a (merge xs ys)
-}

-- lbHead :: Ord a => a -> [a] -> Prop
lbHead a []     = true
lbHead a (x:xs) = holds (less a x) 

-- ordered :: Ord a => [a] -> Prop
ordered []     = true
ordered (x:xs) = lbHead x xs /\ ordered xs

-- prop_merge_lbHead :: Ord a => a -> [a] -> [a] -> Prop
prop_merge_lbHead a xs ys =
  lbHead a xs ==> lbHead a ys ==> lbHead a (merge xs ys)

-- prop_merge_ordered :: OrderedList a -> OrderedList a -> Prop
prop_merge_ordered xs ys =
  ordered xs ==> ordered ys ==> ordered (merge xs ys)

{-
prop_merge_ordered (Ordered xs) (Ordered ys) =
    ordered (merge xs ys)
-}

{-
prop_mergesweep_singleton xs = 
  mergesweep [xs] === [xs]
-}

{- irrelevant, nothing to prove (holds by computation)
prop_msort_empty = 
  msort [] === []
-}

{-
-- OK.
prop_msort_singleton x = 
  msort [x] === [x]
-}

