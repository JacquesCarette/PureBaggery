{-# OPTIONS --without-K --exact-split --safe #-}

-- This is a version of Perm that uses as much of stdlib
-- as possible, while also trying to use its style.
-- Furthermore, this one is based on Setoids rather than baking in
--  on-the-nose equality.
module SetoidPermutations where

open import Data.List.Base as List using (List; []; _∷_; [_]; _++_)
open import Data.List.Properties using (++-identityʳ)
open import Data.Product using (_,_; _,′_; _×_; Σ-syntax; ∃)
open import Level using (Level; _⊔_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Definitions using (Reflexive)
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)
open import Relation.Unary using (_∩_)

open import Partition

  ---------------------------------------------------------------
module _ {o e : Level} {S : Setoid o e} where
  infix 8 _≈_

  private
    X : Set o
    X = Setoid.Carrier S
    _≋_ = Setoid._≈_ S
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
      -> x ≋ y                      -- and x is equivalent to y
      -> (y ∷ xs) ≈ zs              -- then (y ∷ xs) is equivalent to zs
    [] : [] ≈ []

  -- Prove that _≈_ is reflexive
  idPerm : Reflexive _≈_
  idPerm {[]} = []
  idPerm {x ∷ xs} = cons (x ∷ˡ allRPar) idPerm S.refl

  -- and _≈_ respects _≡_
  resp-≡ : forall {xs ys} → xs ≡ ys → xs ≈ ys
  resp-≡ ≡.refl = idPerm

  -- if we can insert equivalent elements into two lists, such the their right
  -- parts are permutation equivalent, the lists are themselves equivalent
  insPerm : forall {x x' xs xs' ys ys'}
    -> [ x ] ↣ xs' ↢ xs
    -> [ x' ] ↣ ys' ↢ ys
    -> x ≋ x'
    -> xs ≈ ys
    -> xs' ≈ ys'
  insPerm (_ ∷ˡ x) insert-y x≋y p = cons insert-y help (S.sym x≋y) where
    help : _
    help with ≡.refl <- isAllRPar x = p
  insPerm {x} {y} {.w ∷ ws} {._ ∷ zs} {ys} {ys'} (w ∷ʳ x↣zs↢ws) x↣ys'↢ys x≋y (cons w↣ys↢ts ws≈ts ≋w) =
    let _ , w↣ys'↢rs , ts↣rs↢x = rotr (_ , w↣ys↢ts , swap x↣ys'↢ys) in
     cons w↣ys'↢rs (insPerm x↣zs↢ws (swap ts↣rs↢x) x≋y ws≈ts) ≋w
     
  -- Permutations are symmetric
  sym : forall {xs ys} -> xs ≈ ys -> ys ≈ xs
  sym (cons x p eq) = insPerm x (_ ∷ˡ allRPar) eq (sym p)
  sym [] = []

  -- if we have a list ws that contains exactly x on the left and xs on the
  -- right, and we have that ws ≈ ys
  -- then we can build a list zs ≈ xs that doesn't contain x which is the
  -- right partition of ys. In other words, we delete x from ws.
  delPerm : forall {x x' xs ys}
         -> <  [ x ]  ↣_↢ xs  ∩  _≈ ys          >
         -> x ≋ x'
         -> <          xs ≈_  ∩ [ x' ] ↣ ys ↢_  >
  delPerm (_ , (_ ∷ˡ pa) , (cons y p eq)) x≋y = _ , p' , {!y!} where
      p' : _
      p' with ≡.refl <- isAllRPar pa = p
  delPerm (_ , (_ ∷ʳ pa) , (cons y p eq)) x≋y =
    let _ , q , z = delPerm (_ , pa , p) x≋y
        _ , a , b = rotr (_ , z , swap y) in
     _ , cons (swap b) q eq , a
{-
  -- permutations are transitive
  trans : forall {xs ys zs} -> xs ≈ ys -> ys ≈ zs -> xs ≈ zs
  trans (pa ∷ p) q =
    let _ , q' , pa′ = delPerm (_ , pa , q) in pa′ ∷ trans p q'
  trans [] [] = []

  -- we can add to the head of a permutation
  congˡ-≈ : {x : X} {xs ys : List X} → xs ≈ ys → (x ∷ xs) ≈ (x ∷ ys)
  congˡ-≈ eq = (_ ∷ˡ allRPar) ∷ eq
  
  -- we can express one of the most basic operations: swapping heads
  -- of equivalent lists
  swap-heads : {x y : X} {ws zs : List X} → ws ≈ zs → (x ∷ y ∷ ws) ≈ (y ∷ x ∷ zs)
  swap-heads {x} {y} ws≈zs = (y ∷ʳ (x ∷ˡ allRPar)) ∷ (y ∷ˡ allRPar) ∷ ws≈zs 

  -- partitions with equivalent rhs induce an append-equivalence
  -- done by casing on both partitions.
  swap-part : {x y : X} {xs ys zs ws : List X} →
    [ x ] ↣ xs ↢ zs → [ y ] ↣ ys ↢ ws → ws ≈ zs → (x ∷ ys) ≈ (y ∷ xs)
  swap-part (_ ∷ˡ x∈xs) (_ ∷ˡ y∈ys) ws≈zs
    with refl <- isAllRPar x∈xs
    with refl <- isAllRPar y∈ys = swap-heads ws≈zs
  swap-part (y ∷ˡ x∈xs) (x ∷ʳ t∈ys) zs≈ys
    with refl <- isAllRPar x∈xs
    with a ∷ b <- zs≈ys = (_ ∷ʳ (y ∷ˡ x∈xs)) ∷ swap-part a t∈ys b
  swap-part (y ∷ʳ x∈xs) (_ ∷ˡ y∈ys) zs≈ws
    with refl <- isAllRPar y∈ys = (_ ∷ʳ (y ∷ʳ x∈xs)) ∷ congˡ-≈ zs≈ws
  swap-part (tt ∷ʳ x∈xs) (uu ∷ʳ y∈ys) zs≈ws
    with a ∷ b <- zs≈ws = (_ ∷ʳ (_ ∷ʳ x∈xs)) ∷ swap-part a y∈ys b
  
  -- permutations play well with concatenation
  ++-cong : {x y u v : List X} → x ≈ y → u ≈ v → (x ++ u) ≈ (y ++ v)
  ++-cong ((x ∷ˡ z) ∷ xs≈ys) u≈v with isAllRPar z
  ... | refl  = insPerm (x ∷ˡ allRPar) (x ∷ˡ allRPar) (++-cong xs≈ys u≈v)
  ++-cong ((y ∷ʳ z) ∷ (x ∷ p) ) u≈v =
    (y ∷ʳ extend-part z) ∷ extend-part x ∷ ++-cong p u≈v 
  ++-cong [] u≈v = u≈v

  -- We can swap two lists. Easiest done by induction on the lists
  ≈-commutative : (xs ys : List X) → (xs ++ ys) ≈ (ys ++ xs)
  ≈-commutative [] ys = resp-≡ (≡.sym (++-identityʳ ys))
  ≈-commutative (x ∷ xs) [] = resp-≡ (++-identityʳ (x ∷ xs))
  ≈-commutative (x ∷ xs) (y ∷ ys) =
    swap-part (insert-into-++ ys) (insert-into-++ xs) (≈-commutative xs ys)

map-perm : {ℓ₁ ℓ₂ : Level} {X : Set ℓ₁} {Y : Set ℓ₂} {xs ys : List X}
   (f : X → Y) → xs ≈ ys →  List.map f xs ≈ List.map f ys
map-perm f (x ∷ eq) = map-par f x ∷ map-perm f eq
map-perm f [] = []

-}
