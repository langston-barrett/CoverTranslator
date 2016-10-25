module Main where
import Property

data T = L | B T T

data C = CB | CL   -- Used Char in original code
type String' = [C]

------------------------------------------------------------
-- Stuff related to +++, our rewrite of ++.

infixr 5 +++
(+++) :: [a] -> [a] -> [a]
[]     +++ ys = ys
(x:xs) +++ ys = x : (xs +++ ys)

-- These need separate proofs
prop_append_nil = forAll (\xs -> ( xs +++ [] ) ===  xs)

-- Proof using guarded coinduction is tricky to express.

-- Proof using fixpoint induction:
-- P(a) = (a xs [] = xs)
-- Base: P(bottom)
-- Step: P(a) => P(app a) where app a []     ys = ys
--                              app a (x:xs) ys = x : a xs ys
-- Both cases require three different cases (_|_, [], :.)

-- Proof using fusion? Probably hard to find.

-- Proof using approximation lemma? Requires expressing the approx
-- function.

-- Proof using ("unguarded") coinduction? Requires expressing what a
-- bisimulation is.

-- Probably FI or CI are the best bets.

prop_append_nil_base_bottom = (bottom +++ []) === bottom
prop_append_nil_base_nil = ([] +++ []) === []
prop_append_nil_step =
  forAll $ \x ->
  forAll $ \xs ->
  (xs +++ []) === xs ==>
    ((x:xs) +++ []) === (x:xs)

prop_append_assoc = 
  forAll $ \xs -> 
  forAll $ \ys -> 
  forAll $ \zs -> 
    (xs +++ (ys +++ zs)) === ((xs +++ ys) +++ zs)

------------------------------------------------------------

pretty :: (T, String') -> String'
pretty (t, cs) = pretty' t +++ cs

pretty' :: T -> String'
pretty'  L        =  [CL]
pretty'  (B l r)  =  [CB] +++ pretty' l +++ pretty' r

parse :: String' -> (T, String')
parse  (CL:cs)  =  (L, cs)
parse  (CB:cs)  =  (B l r, cs'')
  where  (l,  cs' )  =  parse cs
         (r,  cs'')  =  parse cs'

strictify (L, s)     = (L, s)
strictify (B l r, s) = (B l1 (case s1 of CB:s -> r1), s2)
  where (l1, s1)   = strictify (l, CB:s)
        (r1, _:s2) = strictify (r, s1)

prop_base_nil = parse (pretty (L,[])) === (L,[])

prop_test     = parse (pretty (B L L,[])) === (B L L,[])

prop_test_all = forAll $ \xs ->
                parse (pretty (B L L,xs)) === (B L L,xs)

-- Base case: OK for all possible xs (even bottom etc.)
prop_base_all = forAll $ \xs ->
                parse (pretty (L,xs)) === (L,xs)

-- Bottom base case (known to be false)
bottom :: a
bottom = bottom

prop_bottom_all = forAll $ \xs ->
                  parse (pretty (bottom,xs)) === (bottom,xs)

-- Step case: OK for all possible xs (even bottom etc.)
prop_step_all = using [prop_append_assoc] $
                forAll $ \l ->
                forAll $ \r ->
                (forAll $ \xs ->
                 parse (pretty (l,xs)) === (l,xs)) ==>
                (forAll $ \ys ->
                 parse (pretty (r,ys)) === (r,ys)) ==>
                (forAll $ \zs ->
                 parse (pretty (B l r,zs)) === (B l r,zs))

------------------------------------------------------------------------
-- Proof of parse (pretty p) = strictify p using fixpoint induction:

-- Basic property (for all <pair>):
--  P(p, p', s) = parseStep p' (prettyFix (prettyStep p) pair)
--                 === strictifyStep s pair

prettyStep  p  L        =  [CL]
prettyStep  p  (B l r)  =  [CB] +++ p l +++ p r

parseStep  p  (CL:cs)  =  (L, cs)
parseStep  p  (CB:cs)  =  (B l r, cs'')
  where  (l,  cs' )  =  p cs
         (r,  cs'')  =  p cs'

strictifyStep  s  (L, cs)      = (L, cs)
strictifyStep  s  (B l r, cs)  = (B l1 (force s1 r1), s2)
  where (l1, s1)    = s (l, CB:cs)
        (r1, _:s2)  = s (r, s1)

        force s1 r1 = case s1 of CB:cs -> r1

prettyFix p (t, cs) = p t +++ cs

prop_pps_base =
  forAll $ \pair ->
    parseStep bottom (prettyFix (prettyStep bottom) pair)
        === strictifyStep bottom pair

prop_pps_step =
  forAll $ \pair ->
  forAll $ \p ->
  forAll $ \p' ->
  forAll $ \s ->
    (parseStep p' (prettyFix (prettyStep p) pair)
        === strictifyStep s pair
     /\ p bottom === bottom /\ p' bottom === bottom /\ s bottom === bottom
    ) ==>
    (parseStep (parseStep p') (prettyFix (prettyStep (prettyStep p)) pair)
        === strictifyStep (strictifyStep s) pair)

-- ----------------

-- parse (pretty (t, xs)) = (t,xs)  -- for all total finite trees t


main = undefined -- not used

{-
check :: (T, String) -> Bool
check (t, s) = t `eqT` t'   &&   s == s'
   where (t', s') = parsepretty (t,s) 

t1 :: T
t1 = B (B L L) L

main = print (check (t1,""))
-}

-- ----------------

{-
eqT :: T -> T -> Bool
eqT L       L         = True
eqT L       (B l r)   = False
eqT (B l r) L         = False
eqT (B l r) (B l' r') = eqT l l' && eqT r r'
-}

--  |parse . pretty| &|=| |strictify :: (T, String) -> (T, String)|

{- 
strictify :: (T, a) -> (T, a)
strictify (t, a) = t `seq` (t', tTotal `seq` a)
  where (t', tTotal)  = strictify' t
strictify' :: T -> (T, ())
strictify'  L        =  (L, ())
strictify'  (B l r)  =  (B l' (lTotal `seq` r'), lTotal `seq` rTotal)
  where  (l',  lTotal)   =  strictify' l
         (r',  rTotal)   =  strictify' r
-}
