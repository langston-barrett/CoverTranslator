module Add where

import Property

data Nat = Zero | Succ Nat

add x Zero = x
add x (Succ y) = Succ (add x y)
-- The following variant is trickier to prove (at least one case)...
-- add x (Succ y) = add (Succ x) y

{- Backwards axioms, should be pasted into the generated otter files...
   Not needed since we have restricted ourselves to total values.

-equal(c_Add_Succ, bottom).
-equal(c_Add_ZZero, bottom).

equal(app(app(f_Add_add, V_Add_x), app(c_Add_Succ, V_Add_y)), bottom)
  | equal(V_Add_y, app(c_Add_Succ, pred(V_Add_y)))
  | equal(V_Add_y, C_Add_ZZero).

equal(pred(app(c_Add_Succ, X)), X).

-}

prop_add_commutative =
  forAll $ \x ->
    forAll $ \y ->
      add (nat_tf x) (nat_tf y) === add (nat_tf y) (nat_tf x)

-- Let us restrict ourselves to total, finite Nats. Define
-- P(x, y) = add x y = add y x.
--
-- forall total finite x, y :: Nat. P(x, y)
--
--  <=> Induction on y.
--
-- forall total finite x :: Nat. P(x, 0)
-- /\
-- forall total finite x, y :: Nat. P(x, y) -> P(x, Succ y)
--
--  <=> Induction on x in the first branch, case in the second.
--
-- P(0, 0)
-- /\
-- forall total finite x :: Nat. P(x, 0) -> P(Succ x, 0)
-- /\
-- forall total finite y :: Nat. P(0, y) -> P(0, Succ y)
-- /\
-- forall total finite x, y :: Nat. P(Succ x, y) -> P(Succ x, Succ y)
--
--  <=  We can skip type information.
--
-- P(0, 0)
-- /\
-- forall x. P(x, 0) -> P(Succ x, 0)
-- /\
-- forall y. P(0, y) -> P(0, Succ y)
-- /\
-- forall x, y. P(Succ x, y) -> P(Succ x, Succ y)

prop_add_commutative_base =
  add Zero Zero === add Zero Zero

prop_add_commutative_step_1 =
  forAll $ \x ->
    add x Zero === add Zero x ==>
      add (Succ x) Zero === add Zero (Succ x)

-- This step is identical to the previous one, assuming symmetric
-- equality.

prop_add_commutative_step_2 =
  forAll $ \y ->
    add Zero y === add y Zero ==>
      add Zero (Succ y) === add (Succ y) Zero

prop_add_commutative_step_3 =
  using [prop_succ_moveable] $
  forAll $ \x ->
  forAll $ \y ->
    add (Succ x) y === add y (Succ x) ==>
      add (Succ x) (Succ y) === add (Succ y) (Succ x)

-- We need a lemma:
--  Succ x + y = x + Succ y
-- Proof by induction over y.

prop_succ_moveable =
  forAll $ \x ->
  forAll $ \y ->
    add (Succ x) y === add x (Succ y)

prop_succ_moveable_base =
  forAll $ \x ->
    add (Succ x) Zero === add x (Succ Zero)

prop_succ_moveable_step =
  forAll $ \x ->
  forAll $ \y ->
    add (Succ x) y === add x (Succ y) ==>
      add (Succ x) (Succ y) === add x (Succ (Succ y))

-- -- We would like to be able to have this as an axiom:

-- prop_induction_nat_total_finite :: (Nat -> Prop) -> Prop
-- prop_induction_nat_total_finite p =
--   p Zero /\ (forAll $ \x -> p x ==> p (Succ x)) ==>
--     (forAll $ \x -> p (nat_tf x))

-- -- (Or possibly a variant that uses nat_tf also on the left hand
-- -- side. It should only make the proof easier, but I don't know...)

-- -- And this:

-- prop_case_nat p =
--   p Zero /\ (forAll $ \x -> p (Succ x)) ==>
--     (forAll $ \x -> p (nat_c x))

-- -- Then we could state

-- prop_succ_moveable' =
--   using [prop_succ_moveable_base, prop_succ_moveable_step] $
--   prop_induction_nat_total_finite $ \y ->
--   forAll $ \x ->
--     add (Succ x) y === add x (Succ y)

-- -- And similarly for the main property above.

-- -- It would be even better if we could split off the base and step
-- -- cases automatically, of course. That could lead to problems, though:

-- prop_succ_moveable'' =
--   forAll_induction_nat_total_finite $ \y ->
--   forAll $ \x ->
--     add (Succ x) y === add x (Succ y)

-- -- We might not want want proof tactics littering our
-- -- properties. Furthermore the above is incorrect: The resulting
-- -- property should have (nat_tf y) substituted for y. How do we
-- -- check that the variable is only used like that?

-- -- The first approach above should work, though, and the various
-- -- induction schemes and partial identity functions can of course
-- -- be generated automatically.

-- Image: Finite, total Nats plus bottom.

nat_tf :: Nat -> Nat
nat_tf Zero = Zero
nat_tf (Succ x) = Succ $! (nat_tf x)

-- Image: Nat.

nat :: Nat -> Nat
nat Zero = Zero
nat (Succ x) = Succ (nat x)

-- Image: {_|_, Zero} `union` { Succ x | x <- Universe }

nat_c :: Nat -> Nat
nat_c Zero = Zero
nat_c (Succ x) = Succ x
