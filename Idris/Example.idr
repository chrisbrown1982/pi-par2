module Example

import Data.Vect
import Pipar2

fib : Nat -> Nat 
fib 0 = 0
fib 1 = 1
fib n = fib (minus n 1) + fib (minus n 2)

-- modNatLem : modNatNZ 0 0  = 0 

modNatLem2 : modNat 0 (S x) = 0

prf1 : (m : Nat) 
    -> (nw : Nat)
    -> (p : NonZero nw)
    -> Dec (modNatNZ m nw p = 0)
prf1 Z Z p impossible 
prf1 Z (S x) p = Yes Refl
prf1 (S x) Z p  impossible
prf1 (S x) (S y) SIsNonZero = 
    case prf1 x y ?l of 
        Yes prf => ?i 
        No c => ?i2

fibN : (n : Nat) -> (m : Nat) -> (nw : Nat) -> Maybe (Vect m Nat )
fibN n m nw = ?kk 
    -- case 
    --  prf1 m nw of 
    --    Yes prf => Just $ farm fib nw (replicate m n) prf 
    --    No c     => Nothing

