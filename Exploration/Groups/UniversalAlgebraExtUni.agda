module UniversalAlgebraExtUni where

open import Basics
open import UniversalAlgebra
open import ExtUni

module _ {Sort : Set} where
  open Signature Sort

  module _ {sig : Sig}(thy : Theory sig) where

    record UModel : Set where
      open Theory thy
      open Sig EqnSig

      -- mnemonic: 'q' for 'equation'
      field
        Carrier : Sort -> U
        operations : Operations sig (Carrier - El)
        equations  : {i : Sort} -> (q : Opr i) ->
          let ar = arity i q in
          SortDepArity (Carrier - El) ar \ ss ->
          let ev = \ m -> eval sig ar operations ss (sortApply _ ar _ m (tabulate _ var)) in
          Pr (Oq (Carrier i) (ev (leftModel q)) (ev (rightModel q)))

    record _=UModel=>_ (S : UModel)(T : UModel) : Set where
      open UModel
      open Sig sig -- this is likely the wrong to open!
      field
        carrierFun : [: (Carrier S - El) -:> (Carrier T - El) :]
        preservesOprs : (s : Sort)(o : Opr s)(ss : SortTuple (Carrier S - El) (arity s o))
                     -> Pr (Oq (Carrier T s)
                         (carrierFun (sortApply (Carrier S - El) (arity s o) ((Carrier S - El) s)
                           (operations S o) ss))
                         (sortApply (Carrier T - El) (arity s o) ((Carrier T - El) s)
                           (operations T o) (mapSortTuple carrierFun ss)))
                    
