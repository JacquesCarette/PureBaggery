{-# OPTIONS --without-K --safe #-}

module SillyList where

-- The definition of SillyList, map and fold
open import SillyList.Core public
-- The definition of the equivalence relation to use
open import SillyList.Equivalence public
-- Some useful properties of SLmap
open import SillyList.Properties public
-- We need to talk about homomorphisms of Setoid-based monoids
open import SetoidMonoid.Hom
-- These are monoids
open import SillyList.Monoid
-- And we can show an adjointness property that basically says that
-- SillyList is a Free Monoid, aka a proper List
open import SillyList.Categorical

