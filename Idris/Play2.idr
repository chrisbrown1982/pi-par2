data PKind :  Type where
  Su : Nat -> PKind -- suspended (with no. element available)
  O  : PKind -- open (not yet applied)
--   St : PKind -- open streaming

-- e.g. Proc (a -> b) o 
data Proc : Type -> PKind -> Type where

proc : (a -> b) -> Proc (a -> b) O -- primitive
procN : (a -> b) -> (n : Nat) -> Vect n (Proc (a -> b) O) -- derived

data <#> : Proc (a -> b) O -> a -> Proc b (Su 1) -- 
data <##> : Proc (a -> b) O -> Vect n a -> Proc b (Su n) -- distributeL
data <###> : Vect n (Proc (a -> b) O) -> Vect n (Vect m a) -> Vect n (Proc b (Su m))
  -- assume chunked inputs (size m)
data <$> : Proc b (Su (S k)) -> (Proc b (Su k), b) -- sync_stream
<$$> : Vect n (Proc b (Su m)) -> Vect (m*n) b -- derived
data >> : Proc (a -> b) O
       -> Proc (b -> c) O
       -> Proc (a -> c) O

-- Farm, Pipeline, D&C

farmS : (a -> b) -> (nw : Nat) -> Vect m a -> (ok ...) -> Vect nw (Proc b (Su m))
farmS f nw ok xs = qs where
    ps = procN f nw -- : Vect nw (Proc (a -> b) O)
    qs = ps <###> (chunk xs)

farmS' : (a -> b) -> (nw : Nat) -> Vect m a -> (ok ...) -> (Proc b (Su m*nw))
farmS' f nw xs ok =
  let ys = farmS f nw ok xs 
      sp = proc (\zs -> <$$> zs)
  in
    sp <##> ys

farm : (a -> b) -> (nw : Nat) -> Vect m a -> (ok : m `mod` nw == 0) -> Vect n b
farm f nw ok xs = <$$> (farmS f nw ok xs)

-- farm example
fibN : (n : Nat) -> (m : Nat) -> Vect n Nat
fibN n m = farm fib (replicate n 42) ok

{-
  Pipeline is a generalised composition.
  It takes a vector of compatible open/streaming processes
  Returns itself a process representing the pipeline.
  The input processes may be farms, D&Cs, pipeline, &c.

  The idea is that each skeleton may return a suspended process, which conceals the underling structure of (sub)processes.
-}

pipeS : (fs : Vect (S n) (t : Type ** Proc t O)) -- list of stages
    -> (ok : Stages fs a z) -- prf of compatibility; a->z where a -> ... -> z
    -> (xs : Vect m a)
    -> Proc (a -> z) (Su m)
pipeS (f :: fs) ok xs = (foldr (>>) f fs) <##> xs -- >> is associative

pipeS' : (fs : Vect (S n) (t : Type ** Proc t O)) -- list of stages
     -> (ok : Stages fs a z) -- prf of compatibility; a->z where a -> ... -> z
     -> (xs : Vect m a)
     -> Vect m z
pipeS' fs ok xs = <$$> (pipeS fs ok xs)

pipe : (fs : Vect (S n) (b ** c ** (b -> c)))
    -> (ok : StagesFn fs a z)
    -> (xs : Vect m a)
    -> Vect m z
pipe fs ok xs = let (fs' ** ok') = conv fs ok in
  <$$> (pipeS fs' ok' xs)
  
-- Pipe example
imageMerge :: Vect n (Filename, Filename) -> Vect n Image 
imagemerge fNames = pipe [((Filename, Filename) ** (Image, Image) ** read), ((Image, Image) ** Image ** filter)] prf fNames

dc :   (split : a -> Vect n a)
  ->  (join : Vect n b -> b)
  ->  (thres : a -> Bool)
  ->  (solve : a -> b)
  ->  (input : a )
  ->  b
dc split join thre solve input with (thre input)
  | True  = solve input
  | False = 
      let xs = split input 
      re = procN (dc joint thre solve) (length xs)
      reA = re <###> xs
      syn = <$$> reA 
      in join syn  

dcS :  (split : a -> Vect n a)
    ->  (join : Vect n b -> b)
    ->  (thres : a -> Bool)
    ->  (solve : a -> b)
    ->  (input : a )
    ->  Proc b (Su 1)
dcS split join thre solve input with (thre input)
    | True  = (proc solve) <#> input
    | False = 
      let xs = split input 
          re = procN (dc joint thre solve) (length xs) -- : Vect n (Proc (a -> b) O)
          reA = re <###> xs -- : Vect n (Proc b (Su 1))
          syn = <$$> reA -- Vect n b
      in (proc join) <#> syn -- : (Proc b (Su 1))


-- D&C example
fibDC n = dc (\i => [i-1,i-2]) sum (< 5) fib n
