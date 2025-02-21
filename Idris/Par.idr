module Par

import public Data.Vect
-- import public Data.List

public export
data Proc : Type -> Type -> Type where 
    MkProc : (i : Type) -> (o : Type) -> Proc i o 

public export
data ParVect : Nat -> Fin n -> Type -> Type where 
    NilPV : ParVect 0 b a 
    MkParV :(b : Fin k)
         -> (n : Nat)
         -> (prf: LTE n k)
         -> (hd : Vect n a)
         -> (proc : Proc a a) 
        ->  (tl : ParVect m b a)
        -> ParVect (S m) b a

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
                             


-- apply process
-- apply a process to its input
-- semantics are that the input is streamed to the process
-- output is streamed out
public export
(<$>) : (p : Proc a b) -> Vect n a -> Vect n b
-- implementation is built in.

-- puts a function inside a process 
public export
(<*>) : (f : a -> b) -> Proc a b -> Proc a b

public export
parMap : (f : a -> a) -> ParVect n b a -> ParVect n b a 
parMap f NilPV = NilPV 
parMap f (MkParV bo n pr hd proc tl) = 
  let fhd = f <*> proc in 
    MkParV bo n pr (fhd <$> hd) proc (parMap f tl)

seq  : ParVect n b a -> (k ** Vect k a) 
seq NilPV = (Z **  [] )
seq (MkParV bo n pr hd proc tl) = case seq tl of 
                                    (s ** tl') => let r = ((hd ++ tl')) in (plus n s ** r)