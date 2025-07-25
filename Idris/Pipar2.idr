module Pipar2

import Data.Vect

public export
data PKind :  Type where
  Su : Nat -> PKind -- suspended (with no. element available)
  O  : PKind -- open (not yet applied)

-- e.g. Proc (a -> b) o 
public export
data Proc : Type -> PKind -> Type where

public export
proc : (a -> b) -> Proc (a -> b) O -- primitive

public export
procN : (a -> b) -> (n : Nat) -> Vect n (Proc (a -> b) O) -- derived

-- apply


infixr 4 <#>
public export
(<#>) : Proc (a -> b) O -> a -> Proc b (Su 1) 


infixr 4 <##>
public export
(<##>) :    Proc (a -> b) O 
         -> Vect n a 
         -> Proc b (Su n) -- distributeL


infixr 4 <###>
public export
(<###>) : Vect n (Proc (a -> b) O) 
       -> Vect n (Vect m a) 
       -> Vect n (Proc b (Su m))

-- auxilary chunk
public export
chunk : (Vect n a) -> (n : Nat) -> (m : Nat) 
     -> (prf : m `mod` n = 0) -> Vect n (Vect (m `div` n) a)

-- sync
infixr 4 <$>
public export
(<$>) : Proc b (Su (S k)) -> (Proc b (Su k), b) -- sync_stream


infixr 4 <$$>
public export
(<$$>) : Vect n (Proc b (Su m)) -> Vect (m*n) b -- derived

-- composition

infixr 4 <>>>
public export
(>>) : Proc (a -> b) O
    -> Proc (b -> c) O
    -> Proc (a -> c) O

-- skeletons
public export
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

public export
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

public export
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

data Stages : (n : Nat) -> (a : Type) -> (b : Type) -> Type where
  MkStagesNil : Stages Z a b  
  MkStages : (b : Type)
          -> (c : Type)
          -> (s1 : b -> c) 
          -> (ss : Stages n a b)
          -> Stages (S n) a c

spawnStages : Stages n a z -> Vect n (t : Type ** (y : Type ** (Proc (t->y) O)))
spawnStages (MkStagesNil) = []
spawnStages (MkStages a b f ss) =
    let r = spawnStages ss
    in (a ** b ** proc f) :: r


pipeS : (stages : Stages n a z)
     -> (input : Vect m a)
     -> Maybe (Proc (a -> z) (Su m))
-- pipeS MkStagesNil input = ?hole2
pipeS stages input =
    case spawnStages stages of 
        []      => Nothing 
        (f::fs) => let r = foldr (\(a ** b ** s1), (b ** c ** s2) => (a ** c ** s1 >> s2 )) f fs in ?h
    
{-
pipeS : (fs : Vect (S n) (t : Type ** Proc t O)) -- list of stages
    -> (ok : Stages fs a z) -- prf of compatibility; a->z where a -> ... -> z
    -> (xs : Vect m a)
    -> Proc (a -> z) (Su m)
pipeS (f :: fs) ok xs = (foldr (>>) f fs) <##> xs -- >> is associative

-}