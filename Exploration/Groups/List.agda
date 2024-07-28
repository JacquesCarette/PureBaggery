module List where

open import Basics hiding (List; list)
open import ExtUni

postulate
  List : U -> U
  list : (S T : U) -> El ((S `> T) `> (List S `> List T))
  nil : (T : U) -> El (List T)
  cat : (T : U) -> El (List T `> List T `> List T)
  the : (T : U) -> El T -> El (List T)
  nilcat : (T : U)(ts : El (List T)) ->
    Pr (Eq (List T) (List T) (cat T (nil T) ts) ts)
  catnil : (T : U)(ts : El (List T)) ->
    Pr (Eq (List T) (List T) (cat T ts (nil T)) ts)
  catcat : (T : U)(rs ss ts : El (List T)) ->
    Pr (Eq (List T) (List T) (cat T (cat T rs ss) ts) (cat T rs (cat T ss ts)))
  listnil : {S T : U}{f : El (S `> T)} ->
    Pr (Eq (List T) (List T) (list S T f (nil S)) (nil T))
  listcat : {S T : U}{f : El (S `> T)}{xs ys : El (List S)} ->
    Pr (Eq (List T) (List T) (list S T f (cat S xs ys)) (cat T (list S T f xs) (list S T f ys)))
  listthe : {S T : U}{f : El (S `> T)}{s : El S} ->
    Pr (Eq (List T) (List T) (list S T f (the S s)) (the T (f s)))
  listElim : (T : U)(ts : El (List T))(P : El (List T) -> U)
          -> El (P (nil T))
          -> ((s : El T)(ss : El (List T)) -> El (P ss `> P (cat T (the T s) ss)))
          -> El (P ts)
  rev : (T : U) -> El (List T) -> El (List T)
  revnil : (T : U) ->
    Pr (Eq (List T) (List T) (rev T (nil T)) (nil T))
  revthe : (T : U)(t : El T) ->
    Pr (Eq (List T) (List T) (rev T (the T t)) (the T t))
  revcat : (T : U)(ss ts : El (List T)) ->
    Pr (Eq (List T) (List T) (rev T (cat T ss ts)) (cat T (rev T ts) (rev T ss)))
  revrev : (T : U)(ts : El (List T)) ->
    Pr (Eq (List T) (List T) (rev T (rev T ts)) ts)
