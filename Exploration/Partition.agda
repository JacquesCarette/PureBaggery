{-# OPTIONS --without-K --exact-split --safe #-}

-- Partitions of lists. Is implicitly propositional.
module Partition where

open import Data.List.Base as List using (List; []; _∷_; [_]; _++_)
open import Data.Product using (_,_; _,′_; _×_; Σ-syntax; ∃)
open import Level using (Level)
-- open import Relation.Binary.Definitions using (Reflexive)
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_; refl; cong)
open import Relation.Unary using (_∩_)

module _ {ℓ : Level} {X : Set ℓ} where
  -- read as "Possibly T"
  <_> : (X -> Set ℓ) -> Set ℓ
  < T > = ∃ T

  infix 5 <_>

-- Partition a list zs into xs and ys, denoted   xs ↣ zs ↢ ys
-- The constructors say which side the new element goes to.
module _ {ℓ : Level} {X : Set ℓ} where
  infix 10 _↣_↢_

  -- does an element come from the left or right list ?
  data _↣_↢_ : List X -> List X -> List X -> Set ℓ where
    _∷ˡ_ : ∀ x {xs zs ys} -> xs ↣ zs ↢ ys -> (x ∷ xs) ↣ x ∷ zs ↢ ys
    _∷ʳ_ : ∀ y {xs zs ys} -> xs ↣ zs ↢ ys -> xs ↣ y ∷ zs ↢ (y ∷ ys)
    []   : [] ↣ [] ↢ []

  -- swap a partition around
  swap : {xs zs ys : List X} -> xs ↣ zs ↢ ys -> ys ↣ zs ↢ xs
  swap (x ∷ˡ p) = x ∷ʳ swap p
  swap (y ∷ʳ p) = y ∷ˡ swap p
  swap [] = []

  -- If ws can be partitioned into xs and ys, and
  -- ws is also the left part of a partition as (with right part zs),
  -- then xs can also be see as a left part of as,
  -- and ys & zs can be seen as left/right parts.
  -- In other words, this is a "rotates right" action
  rotr : forall {xs ys zs as}
      -> <  xs ↣_↢ ys   ∩  _↣ as ↢ zs  >
      -> <  xs ↣ as ↢_  ∩  ys ↣_↢ zs   >
  rotr (_ , p         , (z ∷ʳ q)) =
    let _ , r , s = rotr (_ , p , q) in _ , z ∷ʳ r , z ∷ʳ s
  rotr (_ , (.y ∷ʳ p) , (y ∷ˡ q)) =
    let _ , r , s = rotr (_ , p , q) in _ , y ∷ʳ r , y ∷ˡ s
  rotr (_ , (.x ∷ˡ p) , (x ∷ˡ q)) =
    let _ , r , s = rotr (_ , p , q) in _ , x ∷ˡ r , s
  rotr (_ , [] , [])              =     _ , [] , []

  -- an equivalent way of writing the signature of rotr
  rotr′ : forall {xs ys zs as}
      -> Σ[ ws ∈ List X ] (xs ↣ ws ↢ ys) × (ws ↣ as ↢ zs)
      -> Σ[ bs ∈ List X ] (xs ↣ as ↢ bs) × (ys ↣ bs ↢ zs)
  rotr′ = rotr

  -- partition where everything is on the right
  allRPar : forall {xs} -> [] ↣ xs ↢ xs
  allRPar {[]}     = []
  allRPar {x ∷ xs} = x ∷ʳ allRPar {xs}

  -- when everything is on the right, both lists are the same
  isAllRPar : forall {xs ys} -> [] ↣ xs ↢ ys -> xs ≡ ys
  isAllRPar (y ∷ʳ p) = cong (y ∷_) (isAllRPar p)
  isAllRPar []       = refl

  -- when everything is on the left, both lists are the same
  isAllLPar : forall {xs ys} -> ys ↣ xs ↢ [] -> xs ≡ ys
  isAllLPar (y ∷ˡ p) = cong (y ∷_) (isAllLPar p)
  isAllLPar []       = refl

  -- given a partition, we can extend it to a partition of an append
  extend-part : {x : X} {xs ys zs : List X} → [ x ] ↣ xs ↢ zs →
    [ x ] ↣ xs ++ ys ↢ (zs ++ ys)
  extend-part (_ ∷ˡ p) with refl <- isAllRPar p = _ ∷ˡ allRPar
  extend-part (y ∷ʳ p) = y ∷ʳ extend-part p
  
  -- inserting into the middle of a partition given by ++
  insert-into-++ : {x : X} (xs : List X) {ys : List X} →
    [ x ] ↣ xs ++ x ∷ ys ↢ (xs ++ ys)
  insert-into-++ [] = _ ∷ˡ allRPar
  insert-into-++ (x ∷ xs) = _ ∷ʳ insert-into-++ xs
  

map-par : {ℓ₁ ℓ₂ : Level} {X : Set ℓ₁} {Y : Set ℓ₂} {xs ys zs : List X}
   (f : X → Y) → xs ↣ zs ↢ ys →  List.map f xs ↣ List.map f zs ↢ List.map f ys
map-par f (x ∷ˡ p) = f x ∷ˡ map-par f p
map-par f (y ∷ʳ p) = f y ∷ʳ map-par f p
map-par f [] = []
  
