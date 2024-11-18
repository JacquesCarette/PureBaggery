module UniversalAlgebraExtUni where

open import Basics
open import UniversalAlgebra
open import ExtUni

module _ {Sort : Set} where
  open Signature Sort

  module HASH (V : Sort -> Nat) where
    # : {sig : Sig}
      {i : Sort}(x : Nat){r : Pr (x < V i)}
        -> FreeOprModel sig (V - Fin - El) i
    # {_}{i} x {r} = var (x , r)

  module _ {sig : Sig}(thy : Theory sig) where

    open Sig sig
    open Theory thy

    record UModel : Set where
      field
        Carrier : Sort -> U
        operations : Operations sig (Carrier - El)
        equations  : PreModel (\ s l r -> Pr (Oq (Carrier s) l r)) operations

    record _=UModel=>_ (S : UModel)(T : UModel) : Set where
      open UModel
      field
        carrierFun : [: (Carrier S - El) -:> (Carrier T - El) :]
        preservesOprs : (s : Sort)(o : Opr s)(ss : SortTuple (Carrier S - El) (arity s o))
                     -> Pr (Oq (Carrier T s)
                         (carrierFun (sortApply (Carrier S - El) (arity s o) ((Carrier S - El) s)
                           (operations S o) ss))
                         (sortApply (Carrier T - El) (arity s o) ((Carrier T - El) s)
                           (operations T o) (mapSortTuple carrierFun ss)))
                    
