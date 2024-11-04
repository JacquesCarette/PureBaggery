module Category where

open import Basics
open import ExtUni
open import Reasoning

record SmallCat : Set₁ where
  field
    Obj : Set
    Hom : Obj -> Obj -> U
    Id : (A : Obj) -> El (Hom A A)
    Comp : {A B C : Obj} -> El (Hom A B `> Hom B C `> Hom A C)
    CompId- : {A B : Obj} -> (f : El (Hom A B)) -> Pr (Oq (Hom A B) (Comp (Id A) f) f)
    Comp-Id : {A B : Obj} -> (f : El (Hom A B)) -> Pr (Oq (Hom A B) (Comp f (Id B)) f)
    CompComp- : {A B C D : Obj} -> (f : El (Hom A B)) -> (g : El (Hom B C)) ->
      (h : El (Hom C D)) -> Pr (Oq (Hom A D) (Comp (Comp f g) h) (Comp f (Comp g h)))

open SmallCat public

UCat : SmallCat
Obj UCat = U
Hom UCat = _`>_
Id UCat _ x = x
Comp UCat f g = f - g
CompId- UCat {A} {B} = refl (A `> B)
Comp-Id UCat {A} {B} = refl (A `> B)
CompComp- UCat {A} {_} {_} {D} f g h = refl (A `> D) _

-- record UEndoFunctor (F : ) : Set where

