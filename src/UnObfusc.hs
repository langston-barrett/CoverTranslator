-- Names are obfuscated quite a bit in GHC-Core.
-- This module gives functions to unobfuscate them.

-- Described in the GHC source code in ghc/compiler/basicTypes/OccName.lhs

module UnObfusc(unObfusc, obfusc) where

import Char(isDigit, chr, digitToInt)

unObfusc :: EncodedString -> UserString
unObfusc s = decode s

obfusc :: UserString -> EncodedString
obfusc s = encode s

-- ----------------
decode :: String -> String
decode [] = []
decode ('Z' : rest) = decode_escape rest
decode ('z' : rest) = decode_escape rest
decode (c   : rest) = c : decode rest

decode_escape :: String -> String
decode_escape ('L' : rest) = '(' : decode rest
decode_escape ('R' : rest) = ')' : decode rest
decode_escape ('M' : rest) = '[' : decode rest
decode_escape ('N' : rest) = ']' : decode rest
decode_escape ('C' : rest) = ':' : decode rest
decode_escape ('Z' : rest) = 'Z' : decode rest
decode_escape ('z' : rest) = 'z' : decode rest
decode_escape ('a' : rest) = '&' : decode rest
decode_escape ('b' : rest) = '|' : decode rest
decode_escape ('c' : rest) = '^' : decode rest
decode_escape ('d' : rest) = '$' : decode rest
decode_escape ('d' : rest) = "zd" ++ decode rest
decode_escape ('e' : rest) = '=' : decode rest
decode_escape ('g' : rest) = '>' : decode rest
decode_escape ('h' : rest) = '#' : decode rest
decode_escape ('i' : rest) = '.' : decode rest
decode_escape ('l' : rest) = '<' : decode rest
decode_escape ('m' : rest) = '-' : decode rest
decode_escape ('n' : rest) = '!' : decode rest
decode_escape ('p' : rest) = '+' : decode rest
decode_escape ('q' : rest) = '\'' : decode rest
decode_escape ('r' : rest) = '\\' : decode rest
decode_escape ('s' : rest) = '/' : decode rest
decode_escape ('t' : rest) = '*' : decode rest
decode_escape ('u' : rest) = '_' : decode rest
decode_escape ('v' : rest) = '%' : decode rest
decode_escape (c : rest)
  | isDigit c = go (digitToInt c) rest
  where
    go n (c : rest) | isDigit c = go (10*n + digitToInt c) rest
    go 0 ('T' : rest)           = "()" ++ (decode rest)
    go n ('T' : rest)           = '(' : replicate (n-1) ',' ++ ')' : 
                                  decode rest
    go 1 ('H' : rest)           = "(# #)" ++ (decode rest)
    go n ('H' : rest)           = '(' : '#' : replicate (n-1) ',' ++ '#' : 
                                    ')' : decode rest
    go n ('U' : rest)           = chr n : decode rest



-- ----------------
type UserString = String        -- As the user typed it
type EncodedString = String     -- Encoded form

encode :: UserString -> EncodedString
encode cs = case maybe_tuple cs of
                Just n  -> n            -- Tuples go to Z2T etc
                Nothing -> go cs
          where
                go []     = []
                go (c:cs) = encode_ch c ++ go cs

unencodedChar :: Char -> Bool   -- True for chars that don't need encoding
unencodedChar 'Z' = False
unencodedChar 'z' = False
unencodedChar c   =  c >= 'a' && c <= 'z'
                  || c >= 'A' && c <= 'Z'
                  || c >= '0' && c <= '9'

encode_ch :: Char -> EncodedString
encode_ch c | unencodedChar c = [c]     -- Common case first

-- Constructors
encode_ch '('  = "ZL"   -- Needed for things like (,), and (->)
encode_ch ')'  = "ZR"   -- For symmetry with (
encode_ch '['  = "ZM"
encode_ch ']'  = "ZN"
encode_ch ':'  = "ZC"
encode_ch 'Z'  = "ZZ"

-- Variables
encode_ch 'z'  = "zz"
encode_ch '&'  = "za"
encode_ch '|'  = "zb"
encode_ch '^'  = "zc"
encode_ch '$'  = "zd"
encode_ch '='  = "ze"
encode_ch '>'  = "zg"
encode_ch '#'  = "zh"
encode_ch '.'  = "zi"
encode_ch '<'  = "zl"
encode_ch '-'  = "zm"
encode_ch '!'  = "zn"
encode_ch '+'  = "zp"
encode_ch '\'' = "zq"
encode_ch '\\' = "zr"
encode_ch '/'  = "zs"
encode_ch '*'  = "zt"
encode_ch '_'  = "zu"
encode_ch '%'  = "zv"
encode_ch c    = 'z' : shows (fromEnum c) "U"


maybe_tuple :: UserString -> Maybe EncodedString

maybe_tuple "(# #)" = Just("Z1H")
maybe_tuple ('(' : '#' : cs) = case count_commas (0::Int) cs of
                                 (n, '#' : ')' : cs) -> Just ('Z' : shows (n+1) "H")
                                 other               -> Nothing
maybe_tuple "()" = Just("Z0T")
maybe_tuple ('(' : cs)       = case count_commas (0::Int) cs of
                                 (n, ')' : cs) -> Just ('Z' : shows (n+1) "T")
                                 other         -> Nothing
maybe_tuple other            = Nothing

count_commas :: Int -> String -> (Int, String)
count_commas n (',' : cs) = count_commas (n+1) cs
count_commas n cs         = (n,cs)
