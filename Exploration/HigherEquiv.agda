module HigherEquiv where

open import Data.Fin using (Fin)
open import Data.Product using (_×_; _,_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Function.Base using (_∘_)
open import Level renaming (suc to lsuc) hiding (zero)

open import GroupActPosition
open import ActionGroupoid using (cong₂)

private
  variable
    ℓ : Level
    
-- surely this is stdlib, but I don't want to search right now
nthProd : ℕ → Set ℓ → Set ℓ
nthProd zero t = ⊤
nthProd (suc n) t = t × nthProd n t -- right nested

liftPred : {A B : Set}
  (R : A → B → Set) (n : ℕ) → nthProd n A → nthProd n B → Set
liftPred _ zero _ _ = ⊤
liftPred R (suc n) (a , s) (b , t) =  R a b × liftPred R n s t 

liftFun : {A B : Set} (f : A → B) (n : ℕ) → nthProd n A → nthProd n B
liftFun f zero x = tt
liftFun f (suc n) (a , s) = f a , liftFun f n s

cartProd : ℕ → Poset → Poset
cartProd n P = record
  { Pos = nthProd n Pos
  ; _c=_ = λ a b → liftPred _c=_ n a b 
  ; rve = liftrve n
  ; asy = liftasy n
  ; xve = lifttrans n
  }
  where
    open Poset P
    _≤_ : {n : ℕ} → nthProd n Pos → nthProd n Pos → Set
    _≤_ {n} = liftPred _c=_ n

    -- all arguments explicit below because they are above
    liftrve : (n : ℕ) (p : nthProd n Pos) → p ≤ p
    liftrve zero    _       = tt
    liftrve (suc n) (p , t) = rve p  , liftrve n t

    liftasy : (n : ℕ) (p q : nthProd n Pos) → p ≤ q → q ≤ p → p ~ q
    liftasy zero p q le gt = r~
    liftasy (suc n) (a , s) (b , t) (a≤b , s-le) (b≤a , t-gt)  = cong₂ _,_ (asy a b a≤b b≤a) (liftasy n s t s-le t-gt)

    lifttrans : (n : ℕ) (p q r : nthProd n Pos) → p ≤ q → q ≤ r → p ≤ r
    lifttrans zero p q r p≤q q≤r = tt
    lifttrans (suc n) (a , s) (b , t) (c , u) (a≤b , xx) (b≤c , yy) = xve a b c a≤b b≤c , lifttrans n s t u xx yy 
    
-- the first version, which is the finite version.
HigherAct : {P : Poset} {G : Group} (A : Action P G) (n : ℕ) → Action (cartProd n P) G
HigherAct {P = P} {G} A n = record
  { _%_ = λ pn g → liftFun (_% g) n pn
  ; _%neu = λ pn → liftEq (_% neu) _%neu n pn
  ; act& = λ pn g h → 
    liftFun (_% (g & h)) n pn              ~[ liftFunEq (_% (g & h)) (λ x → x % g % h) (λ p → act& p g h) n pn >
    liftFun (λ x → x % g % h) n pn         < liftComp (_% g) (_% h) n pn ]~
    liftFun (_% h) n (liftFun (_% g) n pn) [QED]
  ; actc= = λ pn qn g pn≤qn → distrib g n pn qn pn≤qn
  }
  where
    open Poset P
    open Group G
    open Action A
    liftEq : (f : Pos → Pos) → (∀ p → f p ~ p) → (n : ℕ) → ∀ pn → liftFun f n pn ~ pn
    liftEq f pf zero _ = r~
    liftEq f pf (suc n) (a , s) = cong₂ _,_ (pf a) (liftEq f pf n s)
    liftFunEq : (f g : Pos → Pos) → (∀ p → f p ~ g p) → (n : ℕ) → ∀ pn → liftFun f n pn ~ liftFun g n pn
    liftFunEq f g f~g zero pn = r~
    liftFunEq f g f~g (suc n) (a , s) = cong₂ _,_ (f~g a) (liftFunEq f g f~g n s)
    liftComp : (g h : Pos → Pos) (n : ℕ) → ∀ pn → liftFun h n (liftFun g n pn) ~ liftFun (h ∘ g) n pn
    liftComp g h zero pn = r~
    liftComp g h (suc n) (_ , qn) = cong₂ _,_ r~ (liftComp g h n qn)
    -- could generalize to monotone R from _c=_
    distrib : (h : Grp) (n : ℕ) →
              ∀ pn qn → liftPred _c=_ n pn qn → liftPred _c=_ n (liftFun (_% h) n pn) (liftFun (_% h) n qn)
    distrib h zero R _ _ = tt
    distrib h (suc n) (a , s) (b , t) (a≤b , s~t) = actc= a b h a≤b , distrib h n s t s~t
