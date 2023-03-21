{-# OPTIONS --without-K --exact-split --safe #-}

-- Partitions of lists that works over Setoid.
module SetoidPartition where

open import Data.List.Base as List using (List; []; _∷_; [_]; _++_)
open import Data.List.Properties using (++-identityʳ)
open import Data.List.Relation.Binary.Pointwise as PW using (Pointwise)
open import Data.Product using (_,_; _,′_; _×_; Σ-syntax; ∃)
open import Function.Equality as SF using (Π; _⟨$⟩_; _⟶_)
open import Level using (Level; _⊔_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_; cong)
open import Relation.Unary using (_∩_)

module _ {ℓ ℓ′ : Level} {X : Set ℓ} where
  -- read as "Possibly T"
  <_> : (X -> Set ℓ′) -> Set (ℓ′ ⊔ ℓ)
  < T > = ∃ T

  infix 5 <_>

∣_∣ : ∀ {o e} → Setoid o e → Set o
∣ S ∣ = Setoid.Carrier S

-- Partition a list zs into xs and ys, denoted   xs ↣ zs ↢ ys
-- The constructors say which side the new element goes to.
module Build {o e : Level} (XS : Setoid o e) where
  infix 10 _↣_↢_
  open Setoid XS renaming (Carrier to X)

  -- does an element come from the left or right list ?
  data _↣_↢_ : List X -> List X -> List X -> Set (o ⊔ e) where
    onleft  : ∀ x {y xs zs ys} -> xs ↣ zs ↢ ys -> x ≈ y → (x ∷ xs) ↣ y ∷ zs ↢ ys
    onright : ∀ y {z xs zs ys} -> xs ↣ zs ↢ ys -> y ≈ z → xs ↣ z ∷ zs ↢ (y ∷ ys)
    empty   : [] ↣ [] ↢ []

  resp-≈ : forall {xs ys zs xs' ys' zs'} → xs ↣ zs ↢ ys →
    Pointwise _≈_ xs xs' → Pointwise _≈_ ys ys' → Pointwise _≈_ zs zs' →
    xs' ↣ zs' ↢ ys'
  resp-≈ (onleft x p x≈y) (x≈x' PW.∷ xq) yq (z≈z' PW.∷ zq) =
    onleft _ (resp-≈ p xq yq zq) (trans (sym x≈x') (trans x≈y z≈z'))
  resp-≈ (onright y p y≈z) xq (x∼y PW.∷ yq) (x∼y₁ PW.∷ zq) =
    onright _ (resp-≈ p xq yq zq) (trans (sym x∼y) (trans y≈z x∼y₁)) 
  resp-≈ empty PW.[] PW.[] PW.[] = empty
  
  -- swap a partition around
  swap : {xs zs ys : List X} -> xs ↣ zs ↢ ys -> ys ↣ zs ↢ xs
  swap (onleft x p x≈y) = onright x (swap p) x≈y
  swap (onright y p y≈z) = onleft y (swap p) y≈z
  swap empty = empty
  

  -- If ws can be partitioned into xs and ys, and
  -- ws is also the left part of a partition as (with right part zs),
  -- then xs can also be see as a left part of as,
  -- and ys & zs can be seen as left/right parts.
  -- In other words, this is a "rotates right" action
  rotr : forall {xs ys zs as}
      -> <  xs ↣_↢ ys   ∩  _↣ as ↢ zs  >
      -> <  xs ↣ as ↢_  ∩  ys ↣_↢ zs   >
  rotr (f_       , p              , onright y q y≈z) = 
    let _ , r , s = rotr (_ , p , q) in _ , onright y r y≈z , onright y s refl
  rotr (.(x ∷ _) , onleft x' p x'≈x , onleft x q x≈y) = 
    let _ , r , s = rotr (_ , p , q) in _ , onleft x' r (trans x'≈x x≈y) , s
  rotr (.(x ∷ _) , onright y p y≈x , onleft x q x≈y') = 
    let _ , r , s = rotr (_ , p , q) in _ , onright y r (trans y≈x x≈y' ) , onleft y s refl
  rotr (.[]      , empty , empty)           = _ , empty , empty
  
  -- an equivalent way of writing the signature of rotr
  rotr′ : forall {xs ys zs as}
      -> Σ[ ws ∈ List X ] (xs ↣ ws ↢ ys) × (ws ↣ as ↢ zs)
      -> Σ[ bs ∈ List X ] (xs ↣ as ↢ bs) × (ys ↣ bs ↢ zs)
  rotr′ = rotr

  -- partition where everything is on the right
  allRPar : forall {xs} -> [] ↣ xs ↢ xs
  allRPar {[]}     = empty
  allRPar {x ∷ xs} = onright x allRPar refl

  -- when everything is on the right, both lists are the pointwise the same
  isAllRPar : forall {xs ys} -> [] ↣ xs ↢ ys -> Pointwise _≈_ ys xs
  isAllRPar (onright y p y≈z) = y≈z PW.∷ isAllRPar p
  isAllRPar empty             = PW.[]

  -- when everything is on the left, both lists are the same
  isAllLPar : forall {xs ys} -> ys ↣ xs ↢ [] -> Pointwise _≈_ ys xs
  isAllLPar (onleft x p x≈y) = x≈y PW.∷ isAllLPar p
  isAllLPar empty            = PW.[]

  part-resp-++ : {xs ys zs xs' ys' zs' : List X} → xs ↣ ys ↢ zs → xs' ↣ ys' ↢ zs' →
    (xs ++ xs') ↣ (ys ++ ys') ↢ (zs ++ zs')
  part-resp-++ (onleft x p x≈y) q = onleft x (part-resp-++ p q) x≈y
  part-resp-++ (onright y p y≈z) q = onright y (part-resp-++ p q) y≈z
  part-resp-++ empty q = q

  -- missing from Pointwise?
  ≡⇒Pointwise : {xs ys : List X} → xs ≡ ys → Pointwise _≈_ xs ys
  ≡⇒Pointwise {xs} ≡.refl = PW.refl refl {xs}
  
  -- given a partition, we can extend it to a partition of an append
  extend-part : {xs ys zs ws : List X} → ws ↣ xs ↢ zs →
    ws ↣ xs ++ ys ↢ (zs ++ ys)
  extend-part {ys = ys} p = resp-≈ (part-resp-++ p (allRPar {ys})) (≡⇒Pointwise (++-identityʳ _)) (PW.refl refl) (PW.refl refl)

  -- inserting into the middle of a partition given by ++
  insert-into-++ : {x : X} (xs : List X) {ys : List X} → [ x ] ↣ xs ++ x ∷ ys ↢ (xs ++ ys)
  insert-into-++ [] = onleft _ allRPar refl
  insert-into-++ (x ∷ xs) = onright _ (insert-into-++ xs) refl

module _ {o₁ o₂ e₁ e₂ : Level} {XS : Setoid o₁ e₁} {YS : Setoid o₂ e₂} where
  open Setoid XS using () renaming (Carrier to X)
  open Setoid YS using () renaming (Carrier to Y)
  private
    module XS = Setoid XS
    module YS = Setoid YS
    module XP = Build XS
    module YP = Build YS

  map-resp-S≈ : {xs ys zs : List X } (f g : XS ⟶ YS) →
    (∀ {x x' : X} → x XS.≈ x' → f ⟨$⟩ x YS.≈ g ⟨$⟩ x') → xs XP.↣ zs ↢ ys →
    List.map (f ⟨$⟩_) xs YP.↣ List.map (g ⟨$⟩_) zs ↢ List.map (f ⟨$⟩_) ys
  map-resp-S≈ f g resp (XP.onleft x eq x≈y) = YP.onleft (f ⟨$⟩ x) (map-resp-S≈ f g resp eq) (resp x≈y)
  map-resp-S≈ f g resp (XP.onright y eq y≈z) = YP.onright (f ⟨$⟩ y) (map-resp-S≈ f g resp eq) (resp y≈z)
  map-resp-S≈ f g resp XP.empty = YP.empty
  
  map-par :  {xs ys zs : List X }
     (f : XS ⟶ YS) → xs XP.↣ zs ↢ ys →  List.map (f ⟨$⟩_) xs YP.↣ List.map (f ⟨$⟩_) zs ↢ List.map (f ⟨$⟩_) ys
  map-par f par = map-resp-S≈ f f (Π.cong f) par
