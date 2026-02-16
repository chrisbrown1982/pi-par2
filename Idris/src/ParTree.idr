module ParTree

import Pipar2 
import Data.List
import Data.Nat
import Data.Vect

data PTree : (a : Type) 
          -> (Chkd : ChkKind)
          -> Type where

    PTNil : PTree a Flat 

    PNode : (lf : Proc a (Su 1))
         -> (tl : PTree a Flat)
         -> (tr : PTree a Flat)
         -> PTree a Flat


