module FiniteEq where

open import String

open import Basics
open import Membership
open import Finite
open import TabulatedFunctions
open import Universes
open import Decided

----------------------------------------------------------------------------
-- Now we have to construct value equality (over UD)

Enum-Eq : (xs : List String) -> <: _-in xs :> -> (ys : List String) -> <: _-in ys :> -> UD
Enum-Eq (x ,- xs) (_ , ze) (y ,- ys) (_ , ze) = `1
Enum-Eq (x ,- xs) (_ , ze) (y ,- ys) (_ , su j) = `0
Enum-Eq (x ,- xs) (_ , su i) (y ,- ys) (_ , ze) = `0
Enum-Eq (x ,- xs) (_ , su i) (y ,- ys) (_ , su j) = Enum-Eq xs (_ , i) ys (_ , j)

Enum-refl : (xs : List String)(xi : <: _-in xs :>) -> ElD (Enum-Eq xs xi xs xi)
Enum-refl (x ,- xs) (_ , ze) = <>
Enum-refl (x ,- xs) (_ , su i) = Enum-refl xs (_ , i)

-- UF value equality
EqF : (T0 : UF)(t0 : ElF T0)(T1 : UF)(t1 : ElF T1) -> UD
EqF (S0 `>< T0) (s0 , t0) (S1 `>< T1) (s1 , t1) =
  EqF S0 s0 S1 s1 `& EqF (T0 s0) t0 (T1 s1) t1
-- EqF `1 t0 `1 t1 = {!!}
EqF (`E xs) xi (`E ys) yj = Enum-Eq xs xi ys yj
EqF _ _ _ _ = `1

-- some kit before UF type equality
EqListStrings : List String -> List String -> UD
EqListStrings [] [] = `1
EqListStrings (x ,- xs) (y ,- ys) with primStringEquality x y
... | `0 = `0
... | `1 = EqListStrings xs ys
EqListStrings _ _ = `0


-- UF type equality (hurray for tabulated functions!)
infix 30 _=F=_
_=F=_ : UF -> UF -> UD
(S0 `>< T0) =F= (S1 `>< T1) =
  S0 =F= S1 `& `Aa S0 \ s0 -> `Aa S1 (\ s1 -> `Aa (DF (EqF S0 s0 S1 s1)) \ _ -> T0 s0 =F= T1 s1 )
`0 =F= `0 = `1
`1 =F= `1 = `1
`E xs =F= `E ys = EqListStrings xs ys
_ =F= _ = `0 -- off-diagonal: False

coeE : (xs ys : List String) -> ElD (EqListStrings xs ys) -> <: _-in xs :> -> <: _-in ys :>
cohE : (xs ys : List String) (q : ElD (EqListStrings xs ys)) -> (x : <: _-in xs :>) ->
  ElD (Enum-Eq xs x ys (coeE xs ys q x))

coeE (x ,- xs) (y ,- ys) q (_ , i) with primStringEquality x y
coeE (x ,- xs) (y ,- ys) q (_ , ze) | `1 = zee
coeE (x ,- xs) (y ,- ys) q (_ , su i) | `1 = suu (coeE xs ys q (_ , i))

cohE (x ,- xs) (y ,- ys) q (_ , i) with primStringEquality x y
cohE (x ,- xs) (y ,- ys) q (_ , ze) | `1 = <>
cohE (x ,- xs) (y ,- ys) q (_ , su i) | `1 = cohE xs ys q (_ , i)

coeF : (S T : UF) -> ElD (S =F= T) -> ElF S -> ElF T
cohF : (S T : UF) (q : ElD (S =F= T)) (s : ElF S) -> ElD (EqF S s T (coeF S T q s))

coeF (S0 `>< T0) (S1 `>< T1) (qS , qT) (s0 , t0) with coeF S0 S1 qS s0 | cohF S0 S1 qS s0
... | s1 | sQ = s1 , coeF (T0 s0) (T1 s1) (`ffapp _ (`ffapp S1 (`ffapp S0 qT s0) s1) sQ) t0
coeF `1 `1 eq s = <>
coeF (`E xs) (`E ys) eq s = coeE xs ys eq s

cohF (S0 `>< T0) (S1 `>< T1) (qS , qT) (s0 , t0) with coeF S0 S1 qS s0 | cohF S0 S1 qS s0
... | s1 | sQ = sQ , cohF (T0 s0) (T1 s1) (`ffapp _ (`ffapp S1 (`ffapp S0 qT s0) s1) sQ) t0
cohF `1 `1 q s = <>
cohF (`E xs) (`E ys) q s = cohE xs ys q s

-- EqF and =F= are both reflexive. Need helpers as usual
reflE : (xs : List String) (x : <: _-in xs :>) -> ElD (Enum-Eq xs x xs x)
reflE xs (_ , ze) = <>
reflE (x ,- xs) (_ , su i) = reflE xs (_ , i)

reflF : (S : UF) (s : ElF S) -> ElD (EqF S s S s)
reflF (S `>< T) (s , t) = reflF S s , reflF (T s) t
reflF `1 <> = <>
reflF (`E xs) x = reflE xs x

postulate
  -- postulated negation is not very harmful
  NotNotReflF : (S : UF) -> ElD (`Not (S =F= S)) -> Zero
  NotNotRespFF : (S : UF) (s0 s1 : ElF S) (q : ElD (EqF S s0 S s1))
    (T : (s1 : ElF S) (q : ElD (EqF S s0 S s1)) -> UF) ->
    ElD (`Not (T s0 (reflF S s0) =F= T s1 q)) -> Zero
    
ReflF : (S : UF) -> ElD (S =F= S)
ReflF S with lem (S =F= S)
... | inl naw = naughtE (NotNotReflF S naw)
... | inr aye = aye

RespFF : (S : UF) (s0 s1 : ElF S) (q : ElD (EqF S s0 S s1))
    (T : (s1 : ElF S) (q : ElD (EqF S s0 S s1)) -> UF) ->
    ElD (T s0 (reflF S s0) =F= T s1 q)
RespFF S s0 s1 q T with lem (T s0 (reflF S s0) =F= T s1 q)
... | inl naw = naughtE (NotNotRespFF S s0 s1 q T naw)
... | inr aye = aye

-- time for J -- but there are choices!

-- first one: types over UF, motive over UF
J-UF-over-UF : (S : UF) (s0 s1 : ElF S) (q : ElD (EqF S s0 S s1))
  -- deliberate shadow
  (T : (s1 : ElF S) (q : ElD (EqF S s0 S s1)) -> UF) ->
  (t0 : ElF (T s0 (reflF S s0))) -> ElF (T s1 q)
J-UF-over-UF S s0 s1 q T t0 = coeF (T s0 (reflF S s0)) (T s1 q) (RespFF S s0 s1 q T) t0
