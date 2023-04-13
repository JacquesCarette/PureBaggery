module ActionGroupoid where

open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Level

open import Relation.Binary.PropositionalEquality.Core using ()

open import GroupActPosition

open import Categories.Category.Core using (Category)
open import Categories.Category.Groupoid

-- couldn't find these in GroupActPosition
sym : {X : Set} {x y : X} → x ~ y → y ~ x
sym r~ = r~

trans : {X : Set} {x y z : X} → x ~ y → y ~ z → x ~ z
trans x~y y~z = _ ~[ x~y > y~z 

-- Yes, ~$~ can do this, but it's a pain at first order, so
cong₂ : {A B C : Set} {a₁ a₂ : A} {b₁ b₂ : B} (f : A → B → C) → a₁ ~ a₂ → b₁ ~ b₂ → f a₁ b₁ ~ f a₂ b₂
cong₂ f r~ r~ = r~

-- Action Groupoid
ActionGroupoid : {P : Poset} {G : Group} → Action P G → Groupoid 0ℓ 0ℓ 0ℓ
ActionGroupoid {P = P} {G} a = record
  { category = cat
  ; isGroupoid = record
    { _⁻¹ = λ { {p} {q} (g , p%g~q) → inv g ,
                                      q % inv g       < (_% inv g) $~ p%g~q ]~
                                      p % g % inv g   < act& p g (inv g)  ]~
                                      p % (g & inv g) ~[ p %_ $~ (g &inv) >
                                      p % neu         ~[ p %neu >
                                      p               [QED] }
    ; iso = record
      { isoˡ = _ &inv
      ; isoʳ = inv& _
      }
    }
  }
  where
    open Poset P
    open Group G
    open Action a
    cat : Category 0ℓ 0ℓ 0ℓ
    cat = record
      { Obj = Pos
      ; _⇒_ = λ s t → Σ Grp (λ g → s % g  ~ t)
      ; _≈_ = λ x y → proj₁ x ~ proj₁ y
      ; id = λ {p} → neu , (p %neu)
      ; _∘_ = comp
      ; assoc = sym (ass& _ _ _)
      ; sym-assoc = ass& _ _ _
      ; identityˡ = _ &neu
      ; identityʳ = neu& _
      ; identity² = neu& neu
      ; equiv = record { refl = r~ ; sym = sym ; trans = trans }
      ; ∘-resp-≈ = λ f~h g~i → cong₂ _&_ g~i f~h 
      }
      where
        comp : {p q r : Pos} → Σ Grp (λ g → q % g ~ r) → Σ Grp (λ g → p % g ~ q) → Σ Grp (λ g → p % g ~ r)
        comp {p} {q} {r} (g , q%g~r) (h , p%h~q) = h & g ,
          p % (h & g) ~[ act& _ _ _ >
          p % h % g   ~[ (_% g) $~ p%h~q >
          q % g       ~[ q%g~r >          
          r            [QED]
