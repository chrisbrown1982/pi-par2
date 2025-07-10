module Pipar2

import Data.Vect

data PKind :  Type where
  Su : Nat -> PKind -- suspended (with no. element available)
  O  : PKind -- open (not yet applied)

-- e.g. Proc (a -> b) o 
data Proc : Type -> PKind -> Type where

proc : (a -> b) -> Proc (a -> b) O -- primitive
procN : (a -> b) -> (n : Nat) -> Vect n (Proc (a -> b) O) -- derived

-- apply

infixr 4 <#>
(<#>) : Proc (a -> b) O -> a -> Proc b (Su 1) 

infixr 4 <##>
(<##>) :    Proc (a -> b) O 
         -> Vect n a 
         -> Proc b (Su n) -- distributeL

infixr 4 <###>
(<###>) : Vect n (Proc (a -> b) O) 
       -> Vect n (Vect m a) 
       -> Vect n (Proc b (Su m))

-- auxilary chunk

chunk : (Vect n a) -> (n : Nat) -> (m : Nat) 
     -> (prf : m `mod` n = 0) -> Vect n (Vect (m `div` n) a)

-- sync

infixr 4 <$>
(<$>) : Proc b (Su (S k)) -> (Proc b (Su k), b) -- sync_stream

infixr 4 <$$>
(<$$>) : Vect n (Proc b (Su m)) -> Vect (m*n) b -- derived

-- composition
infixr 4 <>>>
(>>) : Proc (a -> b) O
    -> Proc (b -> c) O
    -> Proc (a -> c) O

-- skeletons
farmS : {m : Nat}
     -> (f : a -> b) 
     -> (nw : Nat) 
     -> (xs : Vect m a)
     -> (prf : m `mod` nw = 0) 
     -> Vect nw (Proc b (Su (m `div` nw)))
farmS {m} f nw xs prf = 
    let ps = procN f nw 
        ch = chunk xs nw m prf
        qs = ps <###> ch
    in qs

divLem : {m : Nat} -> {nw : Nat} 
      -> Vect (mult (divNat m nw) nw) a -> Vect m a 
-- needs to be proved

farm : {m : Nat}
    -> (f : a -> b) 
    -> (nw : Nat) 
    -> (xs : Vect m a) 
    -> (prf : m `mod` nw = 0) 
    -> Vect m b
farm f nw xs prf = 
    let r = farmS f nw xs prf in 
        let rr = (<$$>) r in divLem rr 
    
farmSHelper : {nw : Nat} 
           -> {m : Nat}
           -> {b : Type}
           -> Vect nw (Proc b (Su m))
          ->  Vect (mult m nw) b 
farmSHelper {nw} {m} {b} xs = (<$$>) xs

farmS' : {m : Nat}
      -> {b : Type} 
      -> (f : a -> b) 
      -> (nw : Nat) 
      -> (xs : Vect m a) 
      -> (prf : m `mod` nw = 0) 
      -> Proc b (Su m)
farmS' {m} {b} f nw xs prf = 
  let ys = farmS f nw xs prf 
      ysA = (<$$>) ys -- ?pp -- ?oo -- (\zs => (<$$>) zs) -- zs)
      ysA' = divLem ysA
      p    = proc (\x => x)
      r    = p <##> ysA'
  in r

