
[] ++ ys = ys
(x:xs) ++ ys = x : (xs ++ ys)

pack (t,cs) = pack' t ++ cs

pack' L = [O]
pack' (B l r) = [I] ++ (pack' l ++ pack' r)

unpack (O:cs) = (L,cs)
unpack (I:cs) = (B l r, cs)
  where
    (l,cs')  = unpack cs
    (r,cs'') = unpack cs'

