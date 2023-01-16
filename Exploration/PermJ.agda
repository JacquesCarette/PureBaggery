{-# OPTIONS --without-K --exact-split --safe #-}

-- This is a version of Perm that uses as much of stdlib
-- as possible, while also trying to use its style.
module PermJ where

open import Data.List.Base using (List; []; _∷_; [_])
open import Data.Product using (_,_; _,′_; _×_; Σ-syntax; ∃)
open import Level using (Level)
open import Relation.Binary.Definitions using (Reflexive)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong)
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

  infix 10 _≈_

  -- xs ≈ ys means xs is a permutation of ys
  -- Unpacking the definition: a permutation is a list of
  -- left-singleton partitions that says where each item
  -- in the left list gets inserted into the right list.
  data _≈_ : List X -> List X -> Set ℓ where
    _∷_ : forall {x xs ys zs}  -- if we can
      -> [ x ] ↣ zs ↢ ys        -- partition zs into singleton x and ys
      -> xs ≈ ys                -- and xs is equivalent to ys
      -> (x ∷ xs) ≈ zs          -- then (x ∷ xs) is equivalent to zs
    [] : [] ≈ []

  -- Prove that _≈_ is reflexive
  idPerm : Reflexive _≈_
  idPerm {[]} = []
  idPerm {x ∷ xs} = (x ∷ˡ allRPar) ∷ idPerm

  -- and _≈_ respects _≡_
  resp-≡ : forall {xs ys} → xs ≡ ys → xs ≈ ys
  resp-≡ refl = idPerm

  -- if we can insert x into two lists, such the their right
  -- parts are permutation equivalent, the lists are themselves equivalent
  insPerm : forall {x xs xs' ys ys'}
    -> [ x ] ↣ xs' ↢ xs
    -> [ x ] ↣ ys' ↢ ys
    -> xs ≈ ys
    -> xs' ≈ ys'
  insPerm (_ ∷ˡ x) y p = y ∷ help where
    help : _
    help with refl <- isAllRPar x = p
  insPerm (_ ∷ʳ x) y (z ∷ p) = let _ , a , b = rotr (_ , z , swap y) in
    a ∷ insPerm x (swap b) p

  -- Permutations are symmetric
  sym : forall {xs ys} -> xs ≈ ys -> ys ≈ xs
  sym (x ∷ p) = insPerm x (_ ∷ˡ allRPar) (sym p)
  sym [] = []

  -- if we have a list ws that contains exactly x on the left and xs on the
  -- right, and we have that ws ≈ ys
  -- then we can build a list zs ≈ xs that doesn't contain x which is the
  -- right partition of ys. In other words, we delete x from ws.
  delPerm : forall {x xs ys}
         -> <  [ x ]  ↣_↢ xs  ∩  _≈ ys          >
         -> <          xs ≈_  ∩ [ x ] ↣ ys ↢_  >
  delPerm (_ , (_ ∷ˡ pa) , (y ∷ p)) = _ , p' , y where
      p' : _
      p' with refl <- isAllRPar pa = p
  delPerm (_ , (_ ∷ʳ pa) , (y ∷ p)) =
    let _ , q , z = delPerm (_ , pa , p)
        _ , a , b = rotr (_ , z , swap y) in
     _ , swap b ∷ q , a

  -- permutations are transitive
  trans : forall {xs ys zs} -> xs ≈ ys -> ys ≈ zs -> xs ≈ zs
  trans (pa ∷ p) q =
    let _ , q' , pa′ = delPerm (_ , pa , q) in pa′ ∷ trans p q'
  trans [] [] = []
