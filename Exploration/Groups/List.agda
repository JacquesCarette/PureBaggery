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
  rev : (T : U) -> El (List T) -> El (List T)
  revnil : (T : U) ->
    Pr (Eq (List T) (List T) (rev T (nil T)) (nil T))
  revthe : (T : U)(t : El T) ->
    Pr (Eq (List T) (List T) (rev T (the T t)) (the T t))
  revcat : (T : U)(ss ts : El (List T)) ->
    Pr (Eq (List T) (List T) (rev T (cat T ss ts)) (cat T (rev T ts) (rev T ss)))
  revrev : (T : U)(ts : El (List T)) ->
    Pr (Eq (List T) (List T) (rev T (rev T ts)) ts)
