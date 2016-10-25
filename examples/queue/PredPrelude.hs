-- version of PropPrelude where all properties have been turned into predicates
-- Created: abel, 2004-11-12

module PredPrelude where 
import Property

prop_reverse_nil  = (reverse []) ===  []

prop_append_nil_1 xs = ( xs ++ [] ) ===  xs
prop_append_nil_2 xs = ( [] ++ xs ) ===  xs

prop_append_cons x xs ys =
    ((x:xs)++ys) === (x:(xs++ys))

prop_reverse_cons x xs =
    ((reverse xs)++[x]) === (reverse (x:xs)) 

prop_append_assoc xs ys zs =
    (xs ++ (ys ++ zs)) === ((xs ++ ys) ++ zs)

prop_null_1 = null [] === True
prop_null_2 x xs = null (x:xs) === False 

prop_null_true_inv x = 
    (null x === True) ==> (x === [])

prop_null_false_inv x = 
    (null x === False) ==> exists ( \y -> exists ( \ys -> x === (y:ys)))

prop_or x y = ((x || y) === True) <=> ((x === True) \/ (y === True)) 

prop_not_1 x = (not x === True) <=> (x === False)
prop_not_2 x = (not x === False) <=> (x === True)
