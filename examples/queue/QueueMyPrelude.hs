module QueueMyPrelude where 

import Property
import MyPrelude

type Queue a     = [a]
empty            = []
add x q          = my_append q [x]
isEmpty q        = my_null q
front  (x:q)     = x
remove (x:q)     = q

type QueueI a    = ([a], [a])
emptyI           = ([],[])
addI x (f,b)     = flipQ (f, x:b)
isEmptyI (f,b)   = my_null f
frontI  (x:f, b) = x
removeI (x:f, b) = flipQ (f, b)
flipQ ([], b)    = (my_reverse b, [])
flipQ q          = q

retrieve :: QueueI Integer -> Queue Integer
retrieve  (f,b) = my_append f (my_reverse b)

invariant :: QueueI Integer -> Bool
invariant (f,b) = my_null b || not (my_null f)

prop_empty = 
    retrieve emptyI === empty

{-
prop_inv_empty = 
    invariant emptyI === True

prop_inv_cons = 
    forAll $ \x ->
    forAll $ \xs -> (invariant (x:xs, [])) === True 

prop_inv_cons_cons =
    forAll $ \x -> forAll $ \xs -> 
    forAll $ \y -> forAll $ \ys -> (invariant (x:xs, y:ys)) === True 

prop_inv_inv =
    forAll $ \f -> 
    forAll $ \b -> 
       (invariant (f,b) === True) ==>
          (((my_null f) === False) \/ ((my_null b) === True))

{-
prop_add =
    forAll ( \x ->
    forAll ( \q ->
	retrieve (addI x q) === add x (retrieve q) ))
-}

prop_add_nil = 
    forAll $ \x -> 
    forAll $ \b -> 
      retrieve (addI x ([], b)) === add x (retrieve ([], b)) 

prop_add_cons = 
    forAll $ \y  -> 
    forAll $ \ys -> 
    forAll $ \x  -> 
    forAll $ \b  -> 
      retrieve (addI x (y:ys, b)) === add x (retrieve (y:ys, b))

{-
prop_inv_add =
    using [ ] $
    forAll ( \x ->
    forAll ( \f -> forAll ( \b ->
	(invariant (f,b) === True) ==> 
           (invariant (addI x (f,b)) === True) )))
-}

prop_inv_add_nil = 
    forAll $ \a -> invariant (addI a emptyI) === True

prop_inv_add_cons = 
    forAll $ \a ->
    forAll $ \x -> forAll $ \xs -> invariant (addI a (x:xs, [])) === True

prop_inv_add_cons_cons = 
    forAll $ \a ->
    forAll $ \x -> forAll $ \xs -> 
    forAll $ \y -> forAll $ \ys -> 
	   invariant (addI a (x:xs, y:ys)) === True 

prop_isEmpty = 
    forAll $ \f -> forAll $ \b -> 
      (invariant (f,b) === True) ==> 
	   ((isEmptyI (f,b)) === (isEmpty (retrieve (f,b)))) 
-}
