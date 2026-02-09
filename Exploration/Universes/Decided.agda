module Decided where

open import String

open import Basics
open import Thinnings
open import Membership
open import Finite
open import TabulatedFunctions

-- Universe of Decidable Propositions
data UD : Set where
  -- false and true
  `0 `1 : UD

  -- disjunction and conjunction
  -- not strictly needed, but using `#>> would make things unreadable
  _`|_  _`&_ : UD -> UD -> UD

  -- Tabulated functions -- domain in UF
  -- (could we get away with functions?)
  `Aa `Ex : (S : UF) -> (D : ElF S -> UD) -> UD


DF : UD -> UF
DF `0 = `0
DF `1 = `1
DF (D `| E) = DF D `+F DF E
DF (D `& E) = DF D `* DF E
DF (`Aa S D) = S `#> \ s -> DF (D s)
DF (`Ex S D) = S `>< \ s -> DF (D s)

ElD : UD -> Set
ElD = DF - ElF

`Not : UD -> UD
`Not `0 = `1
`Not `1 = `0
`Not (D `| E) = `Not D `& `Not E
`Not (D `& E) = `Not D `| `Not E
`Not (`Aa S D) = `Ex S \ s -> `Not (D s)
`Not (`Ex S D) = `Aa S \ s -> `Not (D s)

`Dec : UD -> UD
`Dec D = `Not D `| D

contradiction : (D : UD) -> ElD (`Not D) -> ElD D -> Zero
contradiction (D `| E) (nD , nE) (inl d) = contradiction D nD d
contradiction (D `| E) (nD , nE) (inr e) = contradiction E nE e
contradiction (D `& E) (inl nD) (d , e) = contradiction D nD d
contradiction (D `& E) (inr nE) (d , e) = contradiction E nE e
contradiction (`Aa S D) (s , naw) aye = contradiction (D s) naw (`ffapp S aye s)
contradiction (`Ex S D) naw (s , aye) = contradiction (D s) (`ffapp S naw s) aye

record _<->_ (P Q : UD) : Set where
  constructor _<<>>_
  field
    l2r : ElD P -> ElD Q
    r2l : ElD Q -> ElD P
open _<->_

OrQ : {A B C D : UD} -> A <-> B -> C <-> D -> (A `| C) <-> (B `| D)
OrQ ab cd .l2r (inl a) = inl (ab .l2r a)
OrQ ab cd .l2r (inr c) = inr (cd .l2r c)
OrQ ab cd .r2l (inl b) = inl (ab .r2l b)
OrQ ab cd .r2l (inr d) = inr (cd .r2l d)

AndQ : {A B C D : UD} -> A <-> B -> C <-> D -> (A `& C) <-> (B `& D)
AndQ ab cd .l2r (a , c) = ab .l2r a , cd .l2r c
AndQ ab cd .r2l (b , d) = ab .r2l b , cd .r2l d

AaQ : {S : UF}{D E : ElF S -> UD} -> ((s : ElF S) -> D s <-> E s) -> `Aa S D <-> `Aa S E
AaQ {S} de .l2r d = `fflam S \ s -> de s .l2r (`ffapp S d s)
AaQ {S} de .r2l e = `fflam S \ s -> de s .r2l (`ffapp S e s)

ExQ : {S : UF}{D E : ElF S -> UD} -> ((s : ElF S) -> D s <-> E s) -> `Ex S D <-> `Ex S E
ExQ de .l2r (s , d) = s , de s .l2r d
ExQ de .r2l (s , e) = s , de s .r2l e

dneg : (D : UD) -> `Not (`Not D) <-> D
dneg `0 = id <<>> id
dneg `1 = id <<>> id
dneg (D `| E) = OrQ (dneg D) (dneg E)
dneg (D `& E) = AndQ (dneg D) (dneg E)
dneg (`Aa S D) = AaQ (\ s -> dneg (D s))
dneg (`Ex S D) = ExQ (\ s -> dneg (D s))

`Lift : {S : Set}(Q : (S -> UD) -> UD) -> Set
`Lift {S} Q = (D : S -> UD) -> ((s : S) -> ElD (`Dec (D s))) -> ElD (`Dec (Q D))

necessarilE : (xs : List String) -> `Lift (`Aa (`E xs))
necessarilE [] D dec = tt
necessarilE (x ,- xs) D dec with dec zee | necessarilE xs (suu - D) (suu - dec)
... | inl naw | _ = inl (zee , naw)
... | inr _ | inl (i , naw) = inl (suu i , naw)
... | inr aye | inr bye = inr (aye , bye)

necessarily : (S : UF) -> `Lift (`Aa S)
necessarily (S `>< T) D dec
  with necessarily S (\ s -> `Aa (T s) \ t -> D (s , t)) (\ s ->
         necessarily (T s) ((s ,_) - D) ((s ,_) - dec))
... | inl (s , t , naw) = inl ((s , t) , naw)
... | inr aye = inr aye
necessarily `0 D dec = tt
necessarily `1 D dec with dec <>
... | inl n = inl (<> , n)
... | inr d = inr d
necessarily (`E xs) D dec = necessarilE xs D dec

decNot : (D : UD) -> ElD (`Dec D) -> ElD (`Dec (`Not D))
decNot D (inl naw) = inr naw
decNot D (inr aye) = inl (dneg D .r2l aye)

possibly : (S : UF) -> `Lift (`Ex S)
possibly S D dec with necessarily S (\ s -> `Not (D s)) (\ s -> decNot (D s) (dec s))
... | inl (s , naw) = inr (s , dneg (D s) .l2r naw)
... | inr aye = inl aye

-- excluded middle
lem : (D : UD) -> ElD (`Not D `| D)
lem `0 = ff
lem `1 = tt
lem (D `| E) with lem D | lem E
... | inr d  | _      = inr (inl d)
... | inl _  | inr e  = inr (inr e)
... | inl nD | inl nE = inl (nD , nE)
lem (D `& E) with lem D | lem E
... | inl d  | _      = inl (inl d)
... | inr _  | inl e  = inl (inr e)
... | inr nD | inr nE = inr (nD , nE)
lem (`Aa S D) = necessarily S D \ s -> lem (D s)
lem (`Ex S D) = possibly S D \ s -> lem (D s)

-- we can actually dig out a witness from non-constructive dneg
witnessDNEG : (D : UD) -> ((ElD D -> Zero) -> Zero) -> ElD D
witnessDNEG D w with lem D
... | inl naw = naughtE (w \ but -> contradiction D naw but)
... | inr aye = aye

