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

{-
-- returns the fold represented in a parallel data type
parFold : (f : a -> a -> a) -> a -> List a -> PList a 
parFold f z l = parFold' (length l) f z l 
    where
        parFold' : Nat -> (a -> a -> a) -> a -> List a -> PList a
        parFold' _ _ _ []  = ?h1  
        parFold' _ _ _ [x] = ?h2 
        parFold' n f z xs  = 
            let n2 = n `divNat` 2 in 
                ?h3
-}