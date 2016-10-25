{-# OPTIONS -fglasgow-exts #-}
-- Recursive natural number a la Parigot (ESOP 88)
-- Test for Core2Agda: universal quantification in constructor
-- Author: Andreas Abel, Oct 2004

-- Current status: LambdaLifting.hs produces error "typeOfBind"


module Parigot where

data N = In (forall a. (N -> a) -> a -> a)

zero :: N
zero = In (\ f a -> a)

succ :: N -> N
succ n = In (\ f a -> f n)

pred :: N -> N
pred (In n) = n id zero

{- I cannot get this right:

rec :: a -> (N -> a -> a) -> N -> a
rec a f n = n rho iota rho
    where iota m  = a
          rho (In y) r = f (In y) (y r iota r)

-}
