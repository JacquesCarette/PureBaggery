module String where

open import Basics

postulate String : Set
{-# BUILTIN STRING String #-}

primitive
  primStringEquality : String → String → Two
