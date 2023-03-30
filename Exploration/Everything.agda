-- Can't use any options like --safe or --without-K since there
-- are exceptions

-- This is mainly a helper to ensure that 'everything' still works.
-- It just tries to load it all up. There's an order to things,
-- and the attempt here is to load up the dependencies first, even
-- though Agda will take care of this. We don't want what used to be
-- dependencies to go unchecked if it turns out that we comment out
-- some use; we don't want code to bit-rot even if it is not currently
-- in use.

module Everything where

-- Some of Conor's stuff
open import FinUni
open import Perm
open import GroupActPosition
-- open import GroupActOrbitPosition -- has some open holes, skip?

-- Jacques' version of similar, split up

-- some kit for monoids
open import SetoidMonoid.Hom

-- SillyList, aka the full Term Algebra version of List
open import SillyList.Core
open import SillyList.Equivalence
open import SillyList.Properties
open import SillyList.Monoid
open import SillyList.Categorical
open import SillyList

-- FreeMonoid, i.e. the List-based Monoid, over propositional equality
open import SetMonoid.Core
open import FreeMonoid

-- Partitions and Permutations over ≡
-- Not actually used, since Bag has to be over Setoid.
open import Partition
open import Permutation

-- Partitions and Permutations over Setoids
open import SetoidPartition
open import SetoidPermutations

-- Bags as a 'silly' term algebra
open import SillyBag

-- Bags as a quotient of lists, induced by permutations
open import Bag

-- open import NoBag -- not ready at all
