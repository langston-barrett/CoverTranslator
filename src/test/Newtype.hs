-- Test for Core2Agda

module Newtype where

newtype L a = L [a]  -- produces currently a "typeOfBind" error

-- data LL a = LL [a] -- this works



