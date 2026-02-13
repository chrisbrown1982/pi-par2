module ParTypes

import Pipar2 
import Data.List
import Data.Nat
import Data.Vect


-- naive version, takes a sequential list and
-- returns a list of processes where each process
-- is the function applied to the list element.

-- on reflection, this makes more sense than parMap2 below
-- the result of the parMap is a parallel data structure
-- representing the parallel map.
parMap : (f : a -> b) -> List a -> PList b Flat
parMap f [] = PNil 
parMap f (hd :: tl) = 
  PCons (proc f <#> hd) (parMap f tl)




-- better to do it this way:
-- have a function that converts a list to a par list
-- then apply parMap to the converted list.
toPList : List a -> PList a Flat
toPList [] = PNil
toPList (x::xs) = 
  PCons (proc (\x => x) <#> x) (toPList xs)

toPListV : Vect n a -> PList a Flat
toPListV [] = PNil
toPListV (x::xs) = 
  PCons (proc (\x => x) <#> x) (toPListV xs)

fromPList : PList a Flat -> List a
fromPList PNil = [] 
fromPList (PCons hd tl) = let (p, r) = (<$>) hd 
                          in r :: fromPList tl



parMap2 : (f : a -> b) -> PList a Flat -> PList b Flat
parMap2 f PNil = PNil 
parMap2 f (PCons hd tl) = PCons (hd <#$> f) (parMap2 f tl)
-- parMap2 f (PConsChk hd tl) = PConsChk (hd <#$> f) (parMap2 f tl)

parMap3 : (f : a -> b) -> PList a chk -> PList b chk 
parMap3 f PNil = PNil
parMap3 f (PCons hd tl) = PCons (hd <#$> f) (parMap3 f tl)
parMap3 f PNilChk = PNilChk
parMap3 f (PConsChk hd tl) = PConsChk (hd <#$> f) (parMap3 f tl)

parMap4 : (f : PList a Flat -> b) -> PList a chk -> PList b chk 



--
-- reduce and parallel map-reduce
-- see https://link.springer.com/chapter/10.1007/978-3-642-32096-5_4?utm_source=researchgate.net&utm_medium=article
--

-- | Creates a list of chunks of length @ d @. The first @ m @ chunks will
-- contain an extra element. 
--
-- Result: list of chunks (blocks)
chunkBalance : Nat    -- ^@ d @: chunk-length
            -> Nat   -- ^@ m @: number of bigger blocks 
            -> List a   -- ^list to be split 
            -> List (List a) -- ^list of chunks (blocks)
chunkBalance d = chunk' where
  chunk' : Nat -> List a -> (List (List a))
  chunk' _ [] = []
  chunk' 0 xs = let (ys,zs) = splitAt d xs in ys :: chunk' 0 zs
  chunk' m xs = let (ys,zs) = splitAt (d+1) xs in ys :: chunk' (minus m 1) zs
    

chunkBalance2 : (n: Nat)        -- chunk-length 
            ->  (m : Nat)       -- number of bigger blocks 
            -> PList a chks -- PList to be split 
            -> (chks2 ** PList a chks2)  -- PList with each element chunked by n?


splitIntoN : Nat      -- ^ number of blocks
          -> List a   -- ^list to be split
          -> List (List a) -- ^list of blocks
splitIntoN n xs = chunkBalance (l `div` n) (l `mod` n) xs where
  l = length xs

splitIntoN2 : (n : Nat) 
          -> PList a chks
          -> (m ** r ** PList a (Chk m r ))  -- with each element being a proc with n things

 
-- simple sequential map reduce (from Eden)
mapRedr : (b -> c -> c) -> c -> (a -> b) -> List a -> c 
mapRedr g e f = (foldr g e) . (map f)


-- re implement as a parallel fold... 
-- enough for map reduce now ... 
-- needs to be associative ... 
foldr2 : (a -> a -> a) -> a 
      -> PList a chks  
      -> Proc a (Su 1) 
foldr2 f a PNil = (proc (\x => x) <#> a)
foldr2 f a (PCons hd tl) = let r = (foldr2 f a tl)
                           in (<#$$>) f hd r
foldr2 f a (PNilChk) = (proc (\x => x) <#> a)
foldr2 f a (PConsChk hd tl) = let hd' = (<$$$>) hd
                                  r   = (proc (\x => x) <#> foldr f a hd')
                                  res = foldr2 f a tl 
                                  u   = (<#$$>) f r res
                              in u
                              


mapRedr2 : (b -> b -> b) -> b -> (a -> b) 
        -> PList a ch 
        -> Proc b (Su 1) 
mapRedr2 g e f = (foldr2 g e) . (parMap3 f)



-- mapReduce converted from Eden
-- converts to PList and back.
parMapRedr : (n : Nat) -> (b -> b -> b) -> b -> (a -> b) 
          -> List a -> b 
parMapRedr n g e f = 
   (foldr g e) . fromPList . (parMap (mapRedr g e f)) . (splitIntoN  n)




lem1 : PList (Proc a (Su 1)) chks -> PList a chks

parMapRedr2 : (n : Nat) -> (g : b -> b -> b) -> (e : b) 
           -> (f : a -> b) 
           -> (i : PList a chks) 
           -> Proc b (Su 1)
parMapRedr2 n g e f i = 
  let (x ** y ** s)  = splitIntoN2 n i -- PList a (Chk x y)
      f' = mapRedr2 g e f -- Plist a Flat -> Proc b (Su 1)
      ma = parMap4 f' s -- PList a ?chk -> PList (Proc b (Su 1)) ?chk
      fo = foldr2 g e (lem1 ma)  -- PList b ?chks -> Proc b (Su 1)
  in fo



{-
chunkBalance2 : Nat    -- ^@ d @: chunk-length
             -> Nat   -- ^@ m @: number of bigger blocks 
             -> List a   -- ^list to be split 
             -> List (List a) -- ^list of chunks (blocks)
chunkBalance2 d = chunk' where
  chunk' : Nat -> List a -> (List (List a))
  chunk' _ [] = []
  chunk' 0 xs = let (ys,zs) = splitAt d xs in ys :: chunk' 0 zs
  chunk' m xs = let (ys,zs) = splitAt (d+1) xs in ys :: chunk' (minus m 1) zs

splitIntoN2 : (m : Nat)      -- ^ number of blocks
          -> PList a n  -- ^list to be split
          -> PList a (m*n) -- ^list of blocks
splitIntoN2 n xs = ?h
  -}   
    -- chunkBalance (l `div` n) (l `mod` n) xs where
    -- l = length xs
    
{-
parMapRedr2 : (n : Nat) -> (b -> b -> b) -> b -> (a -> b) -> PList a n -> Proc b (Su 1) 
parMapRedr2 n g e f = 
   (foldr2 g e) . (parMap2 (mapRedr g e f)) . (splitIntoN2  n)
-}

