module AgdaQueue where 

import Property
import PropPrelude

type Queue a     = [a]
empty            = []
add x q          = q ++ [x]
isEmpty q        = null q
front  (x:q)     = x
remove (x:q)     = q

type QueueI a    = ([a], [a])
emptyI           = ([],[])
addI x (f,b)     = flipQ (f, x:b)
isEmptyI (f,b)   = null f
frontI  (x:f, b) = x
removeI (x:f, b) = flipQ (f, b)
flipQ ([], b)    = (reverse b, [])
flipQ q          = q

retrieve :: QueueI Integer -> Queue Integer
retrieve  (f,b) = f ++ (reverse b)

invariant :: QueueI Integer -> Bool
invariant (f,b) = null b || not (null f)


prop_empty = 
--    using [ prop_reverse_nil, prop_append_nil_1 ] $
    retrieve emptyI === empty

prop_inv_empty = 
--    using [ prop_not_1, prop_or, prop_null_1 ] $
    invariant emptyI === True

prop_inv_cons = 
--    using [ prop_not_1, prop_or, prop_null_1, prop_null_2 ] $
    forAll $ \x ->
    forAll $ \xs -> (invariant (x:xs, [])) === True 

prop_inv_cons_cons =
--    using [ prop_not_1, prop_or, prop_null_1, prop_null_2 ] $
    forAll $ \x -> forAll $ \xs -> 
    forAll $ \y -> forAll $ \ys -> (invariant (x:xs, y:ys)) === True 

prop_inv_inv =
--    using [ prop_null_true_inv, prop_not_1, prop_not_2, prop_or, 
--	    prop_null_1, prop_null_2 ] $
    forAll $ \f -> 
    forAll $ \b -> 
       (invariant (f,b) === True) ==>
          (((null f) === False) \/ ((null b) === True))
{-
prop_add =
    forAll ( \x ->
    forAll ( \q ->
	retrieve (addI x q) === add x (retrieve q) ))
-}

prop_add_nil = 
--    using [ prop_append_nil_1, prop_append_nil_2, 
--            prop_reverse_nil, prop_reverse_cons ] $
    forAll $ \x -> 
    forAll $ \b -> 
      retrieve (addI x ([], b)) === add x (retrieve ([], b)) 

prop_add_cons = 
--    using [ prop_append_assoc, prop_reverse_cons ] $
    forAll $ \y  -> 
    forAll $ \ys -> 
    forAll $ \x  -> 
    forAll $ \b  -> 
      retrieve (addI x (y:ys, b)) === add x (retrieve (y:ys, b))

{-
prop_inv_add =
--    using [ ] $
    forAll ( \x ->
    forAll ( \f -> forAll ( \b ->
	(invariant (f,b) === True) ==> 
           (invariant (addI x (f,b)) === True) )))
-}

prop_inv_add_nil = 
--    using [ prop_not_1, prop_or, prop_null_1, prop_null_2, prop_inv_empty ] $
    forAll $ \a -> invariant (addI a emptyI) === True

prop_inv_add_cons = 
--    using [ prop_not_1, prop_or, prop_null_1, prop_null_2 ] $
    forAll $ \a ->
    forAll $ \x -> forAll $ \xs -> invariant (addI a (x:xs, [])) === True

prop_inv_add_cons_cons = 
--    using [ prop_not_1, prop_or, prop_null_1, prop_null_2 ] $
    forAll $ \a ->
    forAll $ \x -> forAll $ \xs -> 
    forAll $ \y -> forAll $ \ys -> 
	   invariant (addI a (x:xs, y:ys)) === True 

prop_isEmpty = 
--    using [ prop_not_1, prop_not_2, prop_inv_inv,
--	    prop_append_nil_1, prop_reverse_nil, prop_append_cons,
--	    prop_null_1, prop_null_2, prop_null_true_inv,
--	    prop_null_false_inv ] $
    forAll $ \f -> forAll $ \b -> 
      (invariant (f,b) === True) ==> 
	   ((isEmptyI (f,b)) === (isEmpty (retrieve (f,b)))) 

prop_front =
--    using [ prop_not_1, prop_not_2, prop_inv_inv,
--	    prop_append_nil_1, prop_reverse_nil, prop_append_cons,
--	    prop_null_1, prop_null_2, prop_null_true_inv,
--	    prop_null_false_inv ] $
    forAll ( \f -> forAll (\b ->
      ((invariant (f,b) === True) /\ (nt (isEmptyI (f,b) === True))) ==>
         (frontI (f,b) === front (retrieve (f,b)))))



{-
      
prop_front q = invariant q {-&& not (isEmptyI q)-} 
               ==> frontI q == front (retrieve q)

prop_remove q = invariant q && not (isEmptyI q) ==> 
                retrieve (removeI q) == remove (retrieve q)
                                                                                
prop_inv_remove q = invariant q && not (isEmptyI q) ==> invariant (removeI q)

-}

