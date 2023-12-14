module List where

open import Basics
open import ExtUni

postulate
  List : U -> U
  nil : (T : U) -> El (List T)
  cat : (T : U) -> El (List T) -> El (List T) -> El (List T)
  the : (T : U) -> El T -> El (List T)
  nilcat : (T : U)(ts : El (List T)) ->
    Pr (Eq (List T) (List T) (cat T (nil T) ts) ts)
  catnil : (T : U)(ts : El (List T)) ->
    Pr (Eq (List T) (List T) (cat T ts (nil T)) ts)
  catcat : (T : U)(rs ss ts : El (List T)) ->
    Pr (Eq (List T) (List T) (cat T (cat T rs ss) ts) (cat T rs (cat T ss ts)))
