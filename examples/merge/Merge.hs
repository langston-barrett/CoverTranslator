module Merge where
import Property
import PropPrelude
import Simple

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

unitify :: [Simple] -> [[Simple]]
unitify []     = []
unitify (x:xs) = [x] : unitify xs

ordered []           = True
ordered (x:[])       = True
ordered (x:xs@(y:_)) = less x y && ordered xs

-- OK.
prop_mergesweep_singleton = 
  forAll $ \xs->
  mergesweep [xs] === [xs]

-- OK.
prop_msort_empty = 
  msort [] === []

-- OK.
prop_msort_singleton = 
  forAll $ \x->
  msort [x] === [x]

{-
-- Not True (due to possible bottom)
prop_msort_double = 
  forAll $ \x->
  forAll $ \y->
  (msort [x,y] === [x,y]) \/ (msort [x,y] === [y,x]) 

-- Should work when Prop-generating functions are allowed
prop_msort_double_Value = 
  forAll $ \x->
  forAll $ \y->
  isSimpleValue x /\ 
    isSimpleValue y ==> 
      (msort [x,y] === [x,y]) \/ (msort [x,y] === [y,x]) 

-- Should work already (?) but does not
prop_msort_double_Value = 
  forAll $ \x->
  forAll $ \y->
  (x === A \/ x === B \/ x === C) /\ 
    (y === A \/ y === B \/ y === C) ==> 
      (msort [x,y] === [x,y]) \/ (msort [x,y] === [y,x]) 
-}


{-
-- gandalf timeout
prop_correct_merge = 
  forAll $ \xs->
  forAll $ \ys->
  (ordered xs === True) ==> 
    (ordered ys === True) ==> 
      ordered (merge xs ys) === True
-}

-- OK
prop_correct_merge_base = 
  forAll $ \ys->
  (ordered ys === True) ==> 
    ordered (merge [] ys) === True

{-
prop_correct_merge_step = 
  forAll $ \x->
  forAll $ \xs->
  forAll $ \ys->
  ((ordered xs === True) ==> 
     (ordered ys === True) ==> 
       ordered (merge xs ys) === True) ==>
  ((ordered (x:xs) === True) ==> 
     (ordered ys === True) ==> 
       ordered (merge (x:xs) ys) === True)
-}
{-
prop_correct_merge_step = 
  forAll $ \x->
  forAll $ \y->
  forAll $ \xs->
  forAll $ \ys->
  ((ordered xs === True) ==> 
     (ordered (y:ys) === True) ==> 
       ordered (merge xs (y:ys)) === True) ==>
  ((ordered (x:xs) === True) ==> 
     (ordered ys === True) ==> 
       ordered (merge (x:xs) ys) === True) ==>
  ((ordered (x:xs) === True) ==> 
     (ordered (y:ys) === True) ==> 
       ordered (merge (x:xs) (y:ys)) === True)


prop_correct_merge_step = 
  forAll $ \x->
  forAll $ \y->
  forAll $ \xs->
  forAll $ \ys->
  (ordered (x:xs) === True) ==>
  (ordered (y:ys) === True) ==>  
  (ordered (merge xs (y:ys)) === True) ==>
  (ordered (merge (x:xs) ys) === True) ==>
  (ordered (merge (x:xs) (y:ys)) === True)
-}

{-
prop_msort_ordered = 
  forAll $ \xs->
  ordered (msort xs) === True
-}
