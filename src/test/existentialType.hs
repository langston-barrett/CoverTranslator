{-# OPTIONS -fglasgow-exts #-}
-- Test for Core2Agda: existential types

module Existential where

data T = forall a. In (a -> a)
