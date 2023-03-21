{-# OPTIONS --without-K --exact-split --safe #-}

-- This is a version of Perm that uses as much of stdlib
-- as possible, while also trying to use its style.
-- Furthermore, this one is based on Setoids rather than baking in
--  on-the-nose equality.
module SetoidPermutations where

open import Data.List.Relation.Binary.Pointwise as PW using (Pointwise)
open import Data.List.Base as List using (List; []; _∷_; [_]; _++_)
open import Data.List.Properties using (++-identityʳ)
open import Data.Product using (_,_; _,′_; _×_; Σ-syntax; ∃)
open import Function.Equality as SF using (Π; _⟨$⟩_; _⟶_)
open import Level using (Level; _⊔_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Definitions using (Reflexive)
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)
open import Relation.Unary using (_∩_)

open import SetoidPartition

  ---------------------------------------------------------------
module BuildPerm {o e : Level} {S : Setoid o e} where
  infix 8 _≈_

  open Build S -- for Partitions based on Setoids
  
  private
    X : Set o
    X = Setoid.Carrier S
    module S = Setoid S
    
  -- xs ≈ ys means xs is a permutation of ys
  -- Unpacking the definition: a permutation is a list of
  -- left-singleton partitions that says where each item
  -- in the left list gets inserted into the right list.
  -- except that what is inserted is something akin to x.
  data _≈_ : List X -> List X -> Set (o ⊔ e) where
    cons : forall {x y xs ys zs}    -- if we can
      -> [ x ] ↣ zs ↢ ys           -- partition zs into singleton x and ys
      -> xs ≈ ys                    -- and xs is equivalent to ys
      -> x S.≈ y                      -- and x is equivalent to y
      -> (y ∷ xs) ≈ zs              -- then (y ∷ xs) is equivalent to zs
    [] : [] ≈ []

  -- Prove that _≈_ is reflexive
  idPerm : Reflexive _≈_
  idPerm {[]} = []
  idPerm {x ∷ xs} = cons (onleft x allRPar S.refl) idPerm S.refl

  -- and _≈_ respects _≡_
  resp-≡ : forall {xs ys} → xs ≡ ys → xs ≈ ys
  resp-≡ ≡.refl = idPerm

  allRPart⇒Perm : ∀ {xs zs} → [] ↣ zs ↢ xs → zs ≈ xs
  allRPart⇒Perm (onright y p y≈z) = cons (onleft y allRPar S.refl) (allRPart⇒Perm p) y≈z
  allRPart⇒Perm empty = []

  allRPart⇒Perm′ : ∀ {xs zs} → [] ↣ zs ↢ xs → xs ≈ zs
  allRPart⇒Perm′ (onright y p y≈z) = cons (onleft y allRPar y≈z) (allRPart⇒Perm′ p) S.refl
  allRPart⇒Perm′ empty = []

  perm-resp-≈ : forall {xs ys xs' ys'} → xs ≈ ys →
    Pointwise S._≈_ xs xs' → Pointwise S._≈_ ys ys' → xs' ≈ ys'
  perm-resp-≈ (cons part xs≈ys₁ x₂≈y) (x∼y PW.∷ xq) yq =
    cons (resp-≈ part (PW.refl S.refl) (PW.refl S.refl) yq) (perm-resp-≈ xs≈ys₁ xq (PW.refl S.refl)) (S.trans x₂≈y x∼y) 
  perm-resp-≈ [] PW.[] PW.[] = []

  -- if we have a list ws that contains exactly x on the left and xs on the
  -- right, and we have that ws ≈ ys
  -- then we can build a list zs ≈ xs that doesn't contain x which is the
  -- right partition of ys. In other words, we delete x from ws.
  delPerm : forall {x xs ys}
         -> < [ x ]  ↣_↢ xs  ∩  _≈ ys          >
         -> Σ[ y ∈ X ] (Σ[ zs ∈ List X ] (xs ≈ zs × [ y ] ↣ ys ↢ zs × x S.≈ y ))
  delPerm (_ , onleft _ part x , cons x₁ perm x₂) =
    _ , _ ,
      perm-resp-≈ perm (PW.symmetric S.sym (isAllRPar part))
      (PW.refl S.refl) ,
      x₁ ,
      S.trans x (S.sym x₂)
  delPerm (_ , onright y part y≈z , cons part' perm eq-z) =
    let _ , _ , q , z , eq = delPerm (_ , part , perm)
        _ , a , b = rotr (_ , z , swap part' ) in
    _ , _ , cons (swap b) q (S.trans eq-z (S.sym y≈z)) , a , eq

  -- permutations are transitive
  trans : forall {xs ys zs} -> xs ≈ ys -> ys ≈ zs -> xs ≈ zs
  trans (cons pa p x≈y) q =
    let _ , _ , q' , pa′ , eq = delPerm (_ , pa , q) in
    cons pa′ (trans p q') (S.trans (S.sym eq) x≈y)
  trans [] [] = []
  
  -- if we can insert equivalent elements into two lists, such the their right
  -- parts are permutation equivalent, the lists are themselves equivalent
  insPerm : forall {x xs xs' y ys ys'}
    -> [ x ] ↣ xs' ↢ xs
    -> [ y ] ↣ ys' ↢ ys
    -> x S.≈ y
    -> xs ≈ ys
    -> xs' ≈ ys'
  insPerm (onleft _ p x) insert-y x≈y perm =
    cons insert-y (perm-resp-≈ perm (isAllRPar p) (PW.refl S.refl)) (S.trans (S.sym x≈y) x)
  insPerm (onright y p y≈z) insert-y eq (cons p' perm eq-y) =
    let _ , pp , qq = rotr (_ , p' , swap insert-y) in
    cons pp (insPerm p (swap qq) eq perm) (S.trans eq-y y≈z)
    
  -- Permutations are symmetric
  sym : forall {xs ys} -> xs ≈ ys -> ys ≈ xs
  sym (cons x p eq) = insPerm x (onleft _ allRPar S.refl) eq (sym p)
  sym [] = []
  
  -- permutations play well with concatenation
  ++-cong : {xs ys us vs : List X} → xs ≈ ys → us ≈ vs → (xs ++ us) ≈ (ys ++ vs)
  ++-cong (cons part xs≈ys x≈y) us≈vs = cons (part-resp-++ part allRPar) (++-cong xs≈ys us≈vs) x≈y
  ++-cong [] us≈vs = us≈vs

  -- We can swap two lists. Easiest done by induction on the lists
  ≈-commutative : (xs ys : List X) → (xs ++ ys) ≈ (ys ++ xs)
  ≈-commutative [] ys = resp-≡ (≡.sym (++-identityʳ ys))
  ≈-commutative (x ∷ xs) ys = cons (insert-into-++ ys) (≈-commutative xs ys) S.refl

module _ {o₁ o₂ e₁ e₂ : Level} {SX : Setoid o₁ e₁} {SY : Setoid o₂ e₂} where
  private
    module X = Setoid SX
    module Y = Setoid SY
    X = ∣ SX ∣
    Y = ∣ SY ∣
    module BX = BuildPerm {S = SX}
    module BY = BuildPerm {S = SY}
    open BX using (cons; [])
    
  map-perm : {xs ys : List X}
     (f : SX ⟶ SY) → xs BX.≈ ys →  List.map (f ⟨$⟩_) xs BY.≈ List.map (f ⟨$⟩_) ys
  map-perm f (cons x eq x≈y) = BY.cons (map-par f x) (map-perm f eq) (Π.cong f x≈y)
  map-perm f [] = BY.[]

  map-resp-≈ : (f g : SX ⟶ SY) →
      ({x y : X} → x X.≈ y → (f ⟨$⟩ x) Y.≈ (g ⟨$⟩ y)) →
      {xs ys : List X} → xs BX.≈ ys → List.map (f ⟨$⟩_) xs BY.≈ List.map (g ⟨$⟩_) ys
  map-resp-≈ f g resp (cons insert-x xs≈ys x≈y) =
    BY.cons (map-par g insert-x)
            (map-resp-≈ f g resp xs≈ys)
            (Y.trans (Π.cong g x≈y) (Y.sym (resp X.refl)))
  map-resp-≈ f g resp [] = BY.[]
{-
-- two proofs:
-- 1. there is no container that satisfies X ≃ derivative X
-- 2. there is no container that satisfied the Bag interface
-}
