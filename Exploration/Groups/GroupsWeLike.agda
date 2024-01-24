module GroupsWeLike where

open import ExtUni
open import Reasoning
open import Group
open import Iso
open import Basics
-- open import Numbers

module _ where
  Trivial : Group `One
  Trivial = _ -- now there's a proof this IS trivial!!

  IdentityAct : {C : U} (G : Group C) (X : U) -> Action G X
  IdentityAct G X = record
    { act = \ x _ -> x
    ; act-neu = \ x -> refl X x
    ; act-mul = \ x _ _ -> refl X x
    }
  -- Notice that G = Trivial is a special case

  Automorphism : (X : U) -> Group (X <=> X)
  Automorphism X = record
    { neu = idIso X
    ; inv = invIso X X
    ; mul = compIso X X X
    ; mulneu- = \ f -> refl (X <=> X) f 
    ; mulmul- = \ f g h -> refl (X <=> X) (compIso X X X f (compIso X X X g h))
    ; mulinv- = \ f -> after-inv {X} {X} f
    }

  AutAct : (X : U) -> Action (Automorphism X) X
  AutAct X = record
    { act = \ x f -> fwd (iso' {X} {X} f) x
    ; act-neu = \ x -> refl X x
    ; act-mul = \ x f g -> refl X _
    }

  SelfAct : {X : U} (G : Group X) -> Action G X
  SelfAct {X} G = record
    { act     = mul
    ; act-neu = mul-neu
    ; act-mul = \ a b c -> ! mulmul- a b c
    } where
    open Group.Group G -- later rename the file
    open EQPRF X

{-
Cyclic : (n : Nat) -> Group (Fin (su n))
Cyclic n = record
  { neu = 0 , _
  ; inv = plusInverse n
  ; mul = finPlus n
  ; mulneu- = plusAbsorbZero n
  ; mulmul- = {!!}
  ; mulinv- = {!!}
  }
-}
