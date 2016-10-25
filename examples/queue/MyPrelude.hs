module MyPrelude where

import Property

{- Prelude -}
my_null :: [a] -> Bool
my_null []     = True
my_null (x:xs) = False

my_append :: [a] -> [a] -> [a]
my_append []     ys = ys
my_append (x:xs) ys = x : my_append xs ys

-- naive implementation of reverse
my_reverse :: [a] -> [a]
my_reverse []     = []
my_reverse (x:xs) = my_append (my_reverse xs) [x]

prop_my_append_assoc = 
  forAll $ \xs -> forAll $ \ys -> forAll $ \zs -> 
    (my_append xs (my_append ys zs)) === (my_append (my_append xs ys) zs)

prop_my_append_nil = forAll $ \xs -> (my_append xs []) ===  xs

prop_my_null_true_inv = forAll $ \x -> (my_null x === True) ==> (x === [])

prop_my_null_false_inv =
    forAll $ \x -> (my_null x === False) 
             ==> exists ( \y -> exists ( \ys -> x === (y:ys)))
{- End Prelude -}
