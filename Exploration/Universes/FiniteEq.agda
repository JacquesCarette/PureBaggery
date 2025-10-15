module FiniteEq where

open import String

open import Basics
open import Membership
open import Finite
open import TabulatedFunctions
open import Universes

----------------------------------------------------------------------------
-- Now we have to construct value equality

Enum-Eq : (xs : List String) -> <: _-in xs :> -> (ys : List String) -> <: _-in ys :> -> U Props
Enum-Eq (x ,- xs) (_ , ze) (y ,- ys) (_ , ze) = `1
Enum-Eq (x ,- xs) (_ , ze) (y ,- ys) (_ , su j) = `0
Enum-Eq (x ,- xs) (_ , su i) (y ,- ys) (_ , ze) = `0
Enum-Eq (x ,- xs) (_ , su i) (y ,- ys) (_ , su j) = Enum-Eq xs (_ , i) ys (_ , j)

Enum-refl : (xs : List String)(xi : <: _-in xs :>) -> El (Enum-Eq xs xi xs xi)
Enum-refl (x ,- xs) (_ , ze) = <>
Enum-refl (x ,- xs) (_ , su i) = Enum-refl xs (_ , i)

-- UF value equality
EqF : (T0 : UF)(t0 : ElF T0)(T1 : UF)(t1 : ElF T1) -> U Props
EqF (S0 `>< T0) (s0 , t0) (S1 `>< T1) (s1 , t1) =
  EqF S0 s0 S1 s1 `/\ EqF (T0 s0) t0 (T1 s1) t1
-- EqF `1 t0 `1 t1 = {!!}
EqF (`E xs) xi (`E ys) yj = Enum-Eq xs xi ys yj
EqF _ _ _ _ = `1


Enum-EqDec : (xs : List String) -> <: _-in xs :> -> (ys : List String) -> <: _-in ys :> -> Decision UPROPS
Enum-EqDec xs xi ys yj .Naw = Enum-Eq xs xi ys yj `=> `0
Enum-EqDec xs xi ys yj .Aye = Enum-Eq xs xi ys yj
Enum-EqDec (_ ,- _) (_ , ze) (_ ,- _) (_ , ze) .decide = `1 , _
Enum-EqDec (_ ,- _) (_ , ze) (_ ,- _) (_ , su _) .decide = `0 , \ ()
Enum-EqDec (_ ,- _) (_ , su _) (_ ,- _) (_ , ze) .decide = `0 , \ ()
Enum-EqDec (_ ,- xs) (_ , su i) (_ ,- ys) (_ , su j) .decide = Enum-EqDec xs (_ , i) ys (_ , j) .decide
-- would normally expect to say something more detailed and positional, so let's
Enum-EqDec (_ ,- _) (_ , ze) (_ ,- _) (_ , ze) .exclude naw aye = naw aye
Enum-EqDec (_ ,- xs) (_ , su i) (_ ,- ys) (_ , su j) .exclude naw aye =
  Enum-EqDec xs (_ , i) ys (_ , j) .exclude naw aye

EqFDec : (T0 : UF)(t0 : ElF T0)(T1 : UF)(t1 : ElF T1) -> Decision UPROPS
EqFDec T0 t0 T1 t1 .Naw = EqF T0 t0 T1 t1 `=> `0  -- can we do better?
EqFDec T0 t0 T1 t1 .Aye = EqF T0 t0 T1 t1
EqFDec (S0 `>< T0) (s0 , t0) (S1 `>< T1) (s1 , t1) .decide with EqFDec S0 s0 S1 s1 .decide
... | `0 , r = `0 , fst - r
... | `1 , q with EqFDec (T0 s0) t0 (T1 s1) t1 .decide
... | `0 , r = `0 , snd - r
... | `1 , r = `1 , q , r
EqFDec (_ `>< _) _ `1 _ .decide = `1 , _
EqFDec (_ `>< _) _ (`E _) _ .decide = `1 , _
EqFDec `1 _ (_ `>< _) _ .decide = `1 , _
EqFDec `1 <> `1 <> .decide = `1 , _
EqFDec `1 _ (`E _) _ .decide = `1 , _
EqFDec (`E _) _ (_ `>< _) t1 .decide = `1 , _
EqFDec (`E _) _ `1 _ .decide = `1 , _
EqFDec (`E xs) xi (`E ys) yj .decide = Enum-EqDec xs xi ys yj .decide
-- would normally expect to say something more detailed and positional, but that would be long
EqFDec T0 t0 T1 t1 .exclude naw aye = naw aye

-- when we are two enumerations related pointwise?
Enum-Rel : (xs ys : List String) (R : <: _-in xs :> -> <: _-in ys :> -> U Props) -> U Props
Enum-Rel (x ,- xs) (y ,- ys) R = R (x , ze) (y , ze) `/\ Enum-Rel xs ys \ (_ , i) (_ , j) -> R (_ , su i) (_ , su j)
Enum-Rel _         _         _ = `1

-- when are elements of two finite types "pointwise" related?
ElF-Rel : (S0 S1 : UF) -> (ElF S0 -> ElF S1 -> U Props) -> U Props
ElF-Rel (S0 `>< T0) (S1 `>< T1) R =
  ElF-Rel S0 S1 \ s0 s1 -> ElF-Rel (T0 s0) (T1 s1) \ t0 t1 -> R (s0 , t0) (s1 , t1)
-- ElF-Rel `0 `0 R = {!!}
ElF-Rel `1 `1 R = R <> <>
ElF-Rel (`E xs) (`E ys) R = Enum-Rel xs ys R
ElF-Rel _ _ _ = `1

EqListStrings : List String -> List String -> U Props
EqListStrings [] [] = `1
EqListStrings (x ,- xs) (y ,- ys) with primStringEquality x y
... | `0 = `0
... | `1 = EqListStrings xs ys
EqListStrings _ _ = `0

-- UF type equality (hurray for tabulated functions!)
infix 30 _=F=_
_=F=_ : UF -> UF -> U Props
(S0 `>< T0) =F= (S1 `>< T1) =
  S0 =F= S1 `/\
  (S0 `#>> \ s0 -> S1 `#>> \ s1 -> EqF S0 s0 S1 s1 `=> (T0 s0 =F= T1 s1))
`0 =F= `0 = `1
`1 =F= `1 = `1
`E xs =F= `E ys = EqListStrings xs ys
_ =F= _ = `0 -- off-diagonal: False

-- We want to do transport, but first we need to do it on enumerations
-- normally need some postulates... but not in first-order land.
coeE : (xs ys : List String) -> El (EqListStrings xs ys) -> <: _-in xs :> -> <: _-in ys :>
cohE : (xs ys : List String) (q : El (EqListStrings xs ys)) -> (x : <: _-in xs :>) ->
  El (Enum-Eq xs x ys (coeE xs ys q x))

coeE (x ,- xs) (y ,- ys) q (_ , i) with primStringEquality x y
coeE (x ,- xs) (y ,- ys) q (_ , ze) | `1 = zee
coeE (x ,- xs) (y ,- ys) q (_ , su i) | `1 = suu (coeE xs ys q (_ , i))

cohE (x ,- xs) (y ,- ys) q (_ , i) with primStringEquality x y
cohE (x ,- xs) (y ,- ys) q (_ , ze) | `1 = <>
cohE (x ,- xs) (y ,- ys) q (_ , su i) | `1 = cohE xs ys q (_ , i)

coeF : (S T : UF) -> El (S =F= T) -> ElF S -> ElF T
cohF : (S T : UF) (q : El (S =F= T)) (s : ElF S) -> El (EqF S s T (coeF S T q s))

coeF (S0 `>< T0) (S1 `>< T1) (qS , qT) (s0 , t0) =
  let s1 = coeF S0 S1 qS s0 in
  let sq = cohF S0 S1 qS s0 in
  s1 , coeF (T0 s0) (T1 s1) (ffapp S1 (ffapp S0 qT s0) s1 sq) t0
coeF `1 `1 <> <> = <>
coeF (`E xs) (`E ys) q s = coeE xs ys q s

cohF (S0 `>< T0) (S1 `>< T1) (qS , qT) (s0 , t0) =
  let s1 = coeF S0 S1 qS s0 in
  let sq = cohF S0 S1 qS s0 in
  sq , cohF (T0 s0) (T1 s1) (ffapp S1 (ffapp S0 qT s0) s1 sq) t0
cohF `1 `1 <> <> = <>
cohF (`E xs) (`E ys) q s = cohE xs ys q s

-- EqF and =F= are both reflexive. Need helpers as usual
reflE : (xs : List String) (x : <: _-in xs :>) -> El (Enum-Eq xs x xs x)
reflE xs (_ , ze) = <>
reflE (x ,- xs) (_ , su i) = reflE xs (_ , i)

reflF : (S : UF) (s : ElF S) -> El (EqF S s S s)
reflF (S `>< T) (s , t) = reflF S s , reflF (T s) t
reflF `1 <> = <>
reflF (`E xs) x = reflE xs x

postulate
  primStringRefl : (x : String) -> So (primStringEquality x x)

ReflE : (xs : List String) -> El (EqListStrings xs xs)
ReflE [] = <>
ReflE (x ,- xs) with primStringEquality x x | primStringRefl x
... | `1 | q = ReflE xs

-- TODO? we might just be able to not postulate respRF, but it sure has to be
-- mutual with ReflF.
postulate
  -- make the statement anticipate J below
  respRF : (S : UF) (s0 s1 : ElF S) (q : El (EqF S s0 S s1))
    (T : (s1 : ElF S) (q : El (EqF S s0 S s1)) -> UF) ->
    El (T s0 (reflF S s0) =F= T s1 q)

ReflF : (S : UF) -> El (S =F= S)
ReflF (S `>< T) = ReflF S , fflam S \ s0 -> fflam S \ s1 q -> respRF S s0 s1 q \ s2 _ -> T s2
ReflF `0 = <>
ReflF `1 = <>
ReflF (`E xs) = ReflE xs


{- -- nice try, but termination checker unhappy
respRF (R `>< S) (r0 , s0) (r1 , s1) (rq , sq) T = {!!}
respRF `1 <> <> <> T = ReflF (T <>)
respRF (`E xs) s0 s1 q T = help xs s0 s1 q T where
  help : forall xs (s0 s1 : ElF (`E xs))
         (q : El (EqF (`E xs) s0 (`E xs) s1)) (T : ElF (`E xs) -> UF) ->
       El (T s0 =F= T s1)
  help [] (_ , ()) (_ , j) q T
  help (x ,- xs) (_ , ze) (_ , ze) q T = ReflF (T zee)
  help (x ,- xs) (_ , su i) (_ , su j) q T = help xs (_ , i) (_ , j) q \ x -> T (suu x)
-}

-- time for J -- but there are choices!

-- first one: types over UF, motive over UF
J-UF-over-UF : (S : UF) (s0 s1 : ElF S) (q : El (EqF S s0 S s1))
  -- deliberate shadow
  (T : (s1 : ElF S) (q : El (EqF S s0 S s1)) -> UF) ->
  (t0 : ElF (T s0 (reflF S s0))) -> ElF (T s1 q)
J-UF-over-UF S s0 s1 q T t0 = coeF (T s0 (reflF S s0)) (T s1 q) (respRF S s0 s1 q T) t0
