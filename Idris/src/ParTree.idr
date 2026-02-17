module ParTree

import Pipar2 
import Data.List
import Data.Nat
import Data.Vect

data PTree : (a : Type) 
          -> (Chkd : ChkKind)
          -> Type where

    PTLeaf : PTree a Flat 

    PNode : (lf : Proc a (Su 1))
         -> (tl : PTree a Flat)
         -> (tr : PTree a Flat)
         -> PTree a Flat

parMapTree : (f : a -> b) 
          -> (PTree a chks)
          -> (PTree b chks)
parMapTree f PTLeaf = PTLeaf 
parMapTree f (PNode lf tl tr) = PNode (lf <#$> f) 
                                      (parMapTree f tl)
                                      (parMapTree f tr)
