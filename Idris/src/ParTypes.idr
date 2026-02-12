module ParTypes

import Pipar2 
import Data.List
import Data.Nat

-- basic implementation of a parallel list.
-- the cons constructor enforces that the head
-- is in a process.

data PList : (a : Type) -> (p : Nat) -> Type where 
    PNil  : PList a 0
    PCons :  (hd : Proc a (Su 1))
          -> (tl : PList a 0)
          -> PList a 0

    -- not sure we need this case at all... 
    -- if we chunk then can simply cons a process with List a as the head...
    PConsChk :  (hd : Proc a (Su n))
              -> (tl : PList a m) 
              -> PList a (S m)
    

-- naive version, takes a sequential list and
-- returns a list of processes where each process
-- is the function applied to the list element.

-- on reflection, this makes more sense than parMap2 below
-- the result of the parMap is a parallel data structure
-- representing the parallel map.
parMap : (f : a -> b) -> List a -> PList b 0
parMap f [] = PNil
parMap f (hd :: tl) = PCons (proc f <#> hd) (parMap f tl)

-- better to do it this way:
-- have a function that converts a list to a par list
-- then apply parMap to the converted list.
toPList : List a -> PList a 0
toPList [] = PNil 
toPList (x::xs) = PCons (proc (\x => x) <#> x) (toPList xs)

fromPList : PList a 0 -> List a
fromPList PNil = [] 
fromPList (PCons hd tl) = let (p, r) = (<$>) hd 
                          in r :: fromPList tl

parMap2 : (f : a -> b) -> PList a n -> PList b n
parMap2 f PNil = PNil 
parMap2 f (PCons hd tl) = PCons (hd <#$> f) (parMap2 f tl)
parMap2 f (PConsChk hd tl) = PConsChk (hd <#$> f) (parMap2 f tl)

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
    

chunkBalance2 : Nat       -- chunk-length 
            ->  Nat       -- number of bigger blocks 
            -> PList a m  -- PList to be split 
            -> PList a (n * m)
   

splitIntoN : Nat      -- ^ number of blocks
          -> List a   -- ^list to be split
          -> List (List a) -- ^list of blocks
splitIntoN n xs = chunkBalance (l `div` n) (l `mod` n) xs where
  l = length xs

splitIntoN2 : (n : Nat) 
          -> PList a m 
          -> PList a (n*m)

-- simple sequential map reduce (from Eden)
mapRedr : (b -> c -> c) -> c -> (a -> b) -> List a -> c 
mapRedr g e f = (foldr g e) . (map f)


foldr2 : (a -> b -> b) -> b -> PList a n -> Proc b (Su 1) 
foldr2 f a PNil = (proc (\x => x) <#> a)
foldr2 f a (PCons hd tl) = let r = (foldr2 f a tl)
                           in (<#$$>) f hd r

mapRedr2 : (b -> c -> c) -> c -> (a -> b) -> PList a n -> Proc c (Su 1) 
mapRedr2 g e f = (foldr2 g e) . (parMap2 f)

-- mapReduce converted from Eden
-- converts to PList and back.
parMapRedr : (n : Nat) -> (b -> b -> b) -> b -> (a -> b) -> List a -> b 
parMapRedr n g e f = 
   (foldr g e) . fromPList . (parMap (mapRedr g e f)) . (splitIntoN  n)

parMap3 : (PList a n -> b) -> PList a (n*n) -> PList b n

lem1 : PList (Proc a (Su 1)) n -> PList a n

parMapRedr2 : (n : Nat) -> (g : b -> b -> b) -> (e : b) -> (f : a -> b) 
           -> (i : PList a n) 
           -> Proc b (Su 1)
parMapRedr2 n g e f i = 
  let s  = splitIntoN2 n i 
      f' = mapRedr2 g e f
      ma = parMap3 f' s
      fo = foldr2 g e (lem1 ma)
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
