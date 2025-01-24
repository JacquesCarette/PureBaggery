module UniversalAlgebraExtUni where

open import Basics
open import UniversalAlgebra
open import ExtUni

module _ {Sort : Set} where
  open Signature Sort

  module _ {sig : Sig}(thy : Theory sig) where

    record UModel : Set where
      open Theory thy

      -- mnemonic: 'q' for 'equation'
      field
        Carrier : Sort -> U
        operations : Operations sig (Carrier - El)
        equations : (t : Sort) ->
          All
          (/\ \ ga -> /\ \ l r -> SortDepArity (Carrier - El) ga \ ro ->
           let ev = eval sig ga operations ro in
           Pr (Oq (Carrier t) (ev l) (ev r)))
          (zAll (EqnSig t) (equationStatements t))

    record _=UModel=>_ (S : UModel)(T : UModel) : Set where
      open UModel
      field
        carrierFun : [: (Carrier S - El) -:> (Carrier T - El) :]
        preservesOprs : (t : Sort) -> 
          All
          (/\ \ ss -> /\ \ f g -> (vs : All (Carrier S - El) ss) ->
            Pr (Oq (Carrier T t)
                   (carrierFun (sortApply _ ss _ f vs))
                   (sortApply _ ss _ g (mapAll carrierFun vs))))
          (zAll (sig t) (pureAll _,_ <*All*> operations S t <*All*> operations T t))

