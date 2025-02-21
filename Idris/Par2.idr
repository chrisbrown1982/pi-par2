module Par2

import public Data.Vect
-- import public Data.List

-- auxillary vector types and functions

public export 
data VectPart : Nat -> Fin n -> Type -> Type where 
    MkNil : VectPart 0 b a
    MkPar : (b : Fin k)
         -> (prf : LTE n k)
         -> (hd : Vect n a)
         -> (tl : VectPart m b a )
         -> VectPart (S m) b a

public export 
t1 : VectPart 1 (FS (FS (FS (FS FZ)))) Nat
t1 = MkPar (FS (FS (FS (FS FZ)))) 
           (LTESucc (LTESucc (LTESucc (LTESucc LTEZero)))) 
           [1,2,3,4] MkNil
         
public export
t2 : VectPart 2 (FS (FS (FS (FS FZ)))) Nat
t2 = MkPar (FS (FS (FS (FS FZ)))) 
              (LTESucc (LTESucc (LTESucc (LTESucc LTEZero))))  
              [1,2,3,4]
                (MkPar (FS (FS (FS (FS FZ))))  
                    (LTESucc (LTESucc (LTESucc LTEZero)))
                    [1,2,3] MkNil)         

public export
split' : (n : Nat) -> Vect k a -> (s ** (Vect s a, Vect (minus k n) a))
split' n [] = (Z ** ([], [])) 
split' {k} Z xs = (Z ** ([], rewrite (minusZeroRight k) in xs)) 
split' (S c) (x::xs) = case split' c xs of 
                        (s ** (res, leftover)) => (S s ** ((x :: res), leftover)) 
                    
public export
toVectPart : (ch : Nat) 
          -> (bo : Fin ch) 
          -> Vect n a 
          -> Maybe (k ** VectPart k bo a)
toVectPart ch bo [] = Just (Z ** MkNil)
toVectPart Z bo xs = Just (Z ** MkNil)
toVectPart (S c) bo xs = case split' (S c) xs of 
                          (s ** (chunk, rest)) => 
                            case isLTE s (S c) of 
                             No prf => Nothing
                             Yes prf => 
                              case toVectPart (S c) bo rest of 
                               Nothing => Nothing 
                               Just (s ** vp) =>
                                let r =  MkPar bo prf chunk vp
                                in Just ((S s) ** r)

--------------------------------------------------------------------

public export
data Process : Type -> Type -> Type where 
    MkProc : (i : Type) -> (o : Type) -> Process i o 

-- create a suspension, a promise to a result
data Sus : Type -> Type where 
    MkSus : (a : Type) -> Sus a 

-- puts a function inside a process 
public export
process : (f : a -> b) -> Process a b
-- implementation built in


-- apply process
-- apply a process to its input
-- semantics are that the input is streamed to the process
-- output is streamed out
public export
(<$>) : (p : Process a b) -> a-> Sus b
-- implementation is built in.

public export 
spawn : List (Process a b) -> List a -> List b

public export
sync : Sus a -> a

parMap' : (f : a ->b) -> Vect n a -> Vect n (Sus b)
parMap' f [] = []
parMap' f (x::xs) = (process f <$> x ) :: parMap' f xs

public export 
parMap : (f : a -> b) -> Vect n a -> Vect n b 
parMap f [] = [] 
parMap f xs = map sync (parMap' f xs)

public export
parMapPart : (f : a -> b) -> VectPart n bo a -> VectPart n bo b 
parMapPart f MkNil = MkNil 
parMapPart f (MkPar bo prf hd tl) =
    MkPar bo prf (parMap f hd) (parMapPart f tl )

public export
farm : (distr : Vect n a -> VectPart k bo a)
    -> (comb  : VectPart k bo b -> Vect n b)
    -> (f : a -> b)
    -> Vect n a
    -> Vect n b
farm distr comb f input = comb (parMapPart f (distr input))

-- parFold
-- to write

seqDC : (trivial:  a -> Bool) -> (solve : a -> b)
    ->  (split : a -> Vect n a)
    ->  (combine : a -> Vect n b -> b)
    ->  a
    ->  b 
seqDC trivial solve split combine x = rec_dc x
   
 where 
    rec_dc x =  if trivial x then solve x 
                else combine x (map rec_dc (split x))  
-- parDC
parDC : (level : Nat)
    ->  (trivial:  a -> Bool) -> (solve : a -> b)
    ->  (split : a -> Vect n a)
    ->  (combine : a -> Vect n b -> b)
    ->  a
    ->  b 
parDC lvl trivial solve split combine x = par_dc lvl x
    where 
       par_dc : Nat -> a -> b
       par_dc lv x with (lv == 0)
         par_dc lv x | True = seqDC trivial solve split combine x 
         par_dc lv x | False = if trivial x then solve x 
                               else combine x (parMap (par_dc (minus lv 1)) (split x))   
-- pipeline