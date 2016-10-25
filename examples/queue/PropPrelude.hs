module PropPrelude where 
import Property

prop_reverse_nil :: Prop
prop_reverse_nil  =                (reverse []) ===  []

prop_append_nil_1 = forAll $ \xs -> ( xs ++ [] ) ===  xs
prop_append_nil_2 = forAll $ \xs -> ( [] ++ xs ) ===  xs

prop_append_cons = 
  forAll $ \x -> forAll $ \xs -> forAll $ \ys -> 
    ((x:xs)++ys) === (x:(xs++ys))

prop_reverse_cons = 
  forAll $ \x  -> forAll $ \xs ->
    ((reverse xs)++[x]) === (reverse (x:xs)) 

prop_append_assoc = 
  forAll $ \xs -> forAll $ \ys -> forAll $ \zs -> 
    (xs ++ (ys ++ zs)) === ((xs ++ ys) ++ zs)

prop_null_1 = null [] === True
prop_null_2 = forAll $ \x -> forAll $ \xs -> null (x:xs) === False 

prop_null_true_inv = forAll $ \x -> (null x === True) ==> (x === [])

prop_null_false_inv =
    forAll $ \x -> (null x === False) 
             ==> exists ( \y -> exists ( \ys -> x === (y:ys)))

prop_or = 
    forAll $ \x -> 
    forAll $ \y -> 
             ((x || y) === True) <=> ((x === True) \/ (y === True)) 

prop_not_1 = forAll $ \x -> (not x === True) <=> (x === False)
prop_not_2 = forAll $ \x -> (not x === False) <=> (x === True)
