module ParTypes2

import Pipar2 
import Data.List
import Data.Nat
import Data.Vect

parMapFol : -- (n : Nat) 
          (f : Proc a (Su n) -> Proc b (Su 1)) 
       -> PList a (ChkHom n)
       -> PList b Flat
parMapFol f PNil             impossible 
parMapFol f (PCons hd tl)    impossible 
-- parMapFol f PNilChkHet       impossible
-- parMapFol f (PConsChkHet hd tl) impossible
parMapFol f PNilChkHom = PNil
parMapFol f (PConsChkHom hd tl) = let r = f hd 
                                      t = parMapFol f tl
                                  in t

-- re implement as a parallel fold... 
-- enough for map reduce now ... 
-- needs to be associative ... 
foldr2 : (a -> a -> a) -> a 
      -> PList a chks  
      -> Proc a (Su 1) 
foldr2 f a PNil = (proc (\x => x) <#> a)
foldr2 f a (PCons hd tl) = let r = (foldr2 f a tl)
                           in (<#$$>) f hd r
foldr2 f a PNilChkHom = (proc (\x => x) <#> a)
foldr2 f a (PConsChkHom hd tl) = let hd' = (<$$$>) hd
                                     r   = (proc (\x => x) <#> foldr f a hd')
                                     res = foldr2 f a tl 
                                     u   = (<#$$>) f r res
                                 in u

chunkBalance2 : (n: Nat)        -- chunk-length 
            ->  (m : Nat)       -- number of bigger blocks 
            -> PList a chks -- PList to be split 
            -> (chks2 ** PList a chks2)  -- PList with each element chunked by n?

splitIntoN2 : (n : Nat) 
          -> PList a chks
          -> PList a (ChkHom n)  -- with each element being a proc with n things

mapRedr3 : (g : b -> b -> b) 
        -> (e : b)
        -> (f : a -> b) 
        -> (n : Nat)
        -> Proc a (Su n) 
        -> Proc b (Su 1)
mapRedr3 g e f n l = (<#++>) (l <#$> f) g e


parMapRedr2 : (n : Nat) -> (g : b -> b -> b) -> (e : b) 
           -> (f : a -> b) 
           -> (i : PList a chks) 
           -> Proc b (Su 1)
parMapRedr2 n g e f i = 
  let s  = splitIntoN2 n i -- PList a (Chk x y)
      f' = mapRedr3 g e f n-- Plist a Flat -> Proc b (Su 1)
      ma = parMapFol f'  s -- PList a ?chk -> PList (Proc b (Su 1)) ?chk
      fo = foldr2 g e ma  -- PList b ?chks -> Proc b (Su 1)
  in fo