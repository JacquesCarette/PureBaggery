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

open import SetoidPartition

  ---------------------------------------------------------------
module _ {o e : Level} {S : Setoid o e} where
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
{-
  -- if we have a list ws that contains exactly x on the left and xs on the
  -- right, and we have that ws ≈ ys
  -- then we can build a list zs ≈ xs that doesn't contain x which is the
  -- right partition of ys. In other words, we delete x from ws.
  delPerm : forall {x x' xs ys}
         -> <  [ x ]  ↣_↢ xs  ∩  _≈ ys          >
         -> x S.≈ x'
         -> <          xs ≈_  ∩ [ x' ] ↣ ys ↢_  >
  delPerm (_ , (onleft x pa x≈y₁) , (cons {_} {_} {xs} {ys} {zs} y p eq)) x≋y = ys , {!!} , {!!} where
      p' : _
      p' = allRPart⇒Perm′ pa
  delPerm (_ , (onright _ pa _) , (cons y p eq)) x≋y =
    let _ , q , z = delPerm (_ , pa , p) x≋y
        _ , a , b = rotr (_ , z , swap y) in
     _ , cons (swap b) q {!!} , a
-}
  -- permutations are transitive
  trans : forall {xs ys zs} -> xs ≈ ys -> ys ≈ zs -> xs ≈ zs
  trans (cons (onleft _ pa x) p x≈y) (cons x₁ q x₂) = cons {!!} p (S.trans (S.sym x) x≈y)
  trans (cons (onright y pa x) p x≈y) q = cons {!onright ? ? ?!} (trans p {!!}) x≈y
    {- let _ , q' , pa′ = delPerm (_ , pa , q) x≈y in cons pa′ (trans p q') S.refl -}
  trans [] [] = []

  -- if we can insert equivalent elements into two lists, such the their right
  -- parts are permutation equivalent, the lists are themselves equivalent
  insPerm : forall {x x' xs xs' ys ys'}
    -> [ x ] ↣ xs' ↢ xs
    -> [ x' ] ↣ ys' ↢ ys
    -> x S.≈ x'
    -> xs ≈ ys
    -> xs' ≈ ys'
  insPerm (onleft _ x x≈y) insert-y x≋y p = cons insert-y help (S.trans (S.sym x≋y) x≈y) where
    help : _
    help = {!allRPart⇒Perm x!} -- with ≡.refl <- isAllRPar x = p
  insPerm {x} {y} {.w ∷ ws} {._ ∷ zs} {ys} {ys'} (onright w x↣zs↢ws _) x↣ys'↢ys x≋y (cons w↣ys↢ts ws≈ts ≋w) =
    let _ , w↣ys'↢rs , ts↣rs↢x = rotr (_ , w↣ys↢ts , swap x↣ys'↢ys) in
     cons w↣ys'↢rs (insPerm x↣zs↢ws (swap ts↣rs↢x) x≋y ws≈ts) {!!}
     
  -- Permutations are symmetric
  sym : forall {xs ys} -> xs ≈ ys -> ys ≈ xs
  sym (cons x p eq) = insPerm x (onleft _ allRPar S.refl) eq (sym p)
  sym [] = []

{-
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
