module PropPrelude where 
import Property

-- These follow from the definition of append (I think)
prop_append_nil   = forAll (\xs -> ( [] ++ xs ) ===  xs)
prop_append_cons  = forAll (\x -> 
                    forAll (\xs -> 
                    forAll (\ys -> 
                    ((x:xs) ++ ys) === (x:(xs++ys)))))

----------------
-- These need separate proofs
prop_append_nil_2 = forAll (\xs -> ( xs ++ [] ) ===  xs)

prop_append_assoc = 
  forAll $ \xs -> 
  forAll $ \ys -> 
  forAll $ \zs -> 
    (xs ++ (ys ++ zs)) === ((xs ++ ys) ++ zs)
