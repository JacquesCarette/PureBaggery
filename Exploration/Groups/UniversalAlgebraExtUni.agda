module UniversalAlgebraExtUni where

open import Basics
open import UniversalAlgebra
open import ExtUni

module _ {Sort : Set} where
  open Signature Sort

  module _ {sig : Sig}(thy : Theory sig) where
  
    Equations : (Ca : Sort -> U)(ops : Operations sig (Ca - El))(t : Sort)(ES : List (List Sort))(QS : Eqns sig ES t) -> Set
    Equations Ca ops t ES QS =
      All
        (/\ \ ga -> /\ \ l r -> SortDepArity (Ca - El) ga \ ro ->
         let ev = eval sig ga ops ro in
         Pr (Oq (Ca t) (ev l) (ev r)))
        (zAll ES QS)

    record UModel : Set where
      open Theory thy


      -- mnemonic: 'q' for 'equation'
      field
        Carrier : Sort -> U
        operations : Operations sig (Carrier - El)
        equations : (t : Sort) -> Equations Carrier operations t (EqnSig t) (eqns t)

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

  module _ {sig : Sig}{thy : Theory sig}{ext : SigExtension sig}
           (thyExt : TheoryExtension thy ext)
           where
    open Theory
    open TheoryExtension thyExt
    open UModel

    UForget : UModel extTheory -> UModel thy
    Carrier (UForget m) = Carrier m
    operations (UForget m) t = select (extIsBigger ext t) (operations m t)
    equations (UForget m) t = help {EqnSig thy t} {fst (EqnSigExt t)} (snd (EqnSigExt t)) (eqns thy t) (eqnsExt t) (equations m t)
      where
      help : forall {wee big} (th : wee <= big) -> let (comp , opth) , apart = th -not in
             (oqs : Eqns sig wee t)(nqs : Eqns (ext - fst) comp t)
         ->  Equations extTheory (Carrier m) (operations m) t big
               (mapAll (embed (ext - snd) >><< embed (ext - snd)) oqs /< apart >\ nqs) 
         ->  Equations thy (Carrier m) (\ t -> select (snd (ext t)) (operations m t)) t wee oqs
      help (a ^- th) oqs (nq , nqs) (mq , mqs) = help th oqs nqs mqs
      help (a ,- th) (oq , oqs) nqs (mq , mqs) = {!mq!} , help th oqs nqs mqs
                                              -- ^^^^^ HERE
      help [] <> <> <> = <>
