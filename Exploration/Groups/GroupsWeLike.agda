module GroupsWeLike where

open import ExtUni
open import Reasoning
open import Algebras
open import Actions
open import Iso
open import Basics
open import Numbers

module _ where
  Trivial : Group `One
  Trivial = _ -- now there's a proof this IS trivial!!

  module _ {C : U} (G : Group C) where
    open ACTION G
    
    IdentityAct :  (X : U) -> Action X
    IdentityAct X = record
      { act = \ x _ -> x
      ; act-neu = \ x -> refl X x
      ; act-mul = \ x _ _ -> refl X x
      }
    -- Notice that G = Trivial is a special case

    SelfAct : Action C
    SelfAct = record
      { act     = mul
      ; act-neu = mul-neu
      ; act-mul = \ a b c -> ! mulmul- a b c
      } where
      open Algebras.Group G -- later rename the file
      open EQPRF C

    ActZero : Action `Zero
    ActZero = record
      { act = \ ()
      ; act-neu = _
      ; act-mul = _
      }

  module _ (X : U) where
  
    Automorphism : Group (X <=> X)
    Automorphism = record
      { neu = idIso X
      ; inv = invIso X X
      ; mul = compIso X X X
      ; mulneu- = \ f -> refl (X <=> X) f 
      ; mulmul- = \ f g h -> refl (X <=> X) (compIso X X X f (compIso X X X g h))
      ; mulinv- = \ f -> after-inv {X} {X} f
      }
 
    open ACTION Automorphism

    AutAct : Action X
    AutAct = record
      { act = \ x f -> fwd (iso' {X} {X} f) x
      ; act-neu = \ x -> refl X x
      ; act-mul = \ x f g -> refl X _
      }


Cyclic : (n : Nat) -> Group (FinSu n)
Cyclic n = record
  { neu = G.zeF
  ; inv = G.inv
  ; mul = G._+F_
  ; mulneu- = G.ze+
  ; mulmul- = G.assocF
  ; mulinv- = G.inv+
  }
  where
    module G = BuildFin n

