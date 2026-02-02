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

{-  -- should we deal directly? let's try not
ElD `0 = Zero
ElD `1 = One
ElD (D `| E) = ElD D + ElD E
ElD (D `& E) = ElD D * ElD E
ElD (`Aa S D) = S #> \ s -> ElD (D s)
ElD (`Ex S D) = ElF S >< \ s -> ElD (D s)
-}


{-
-- Preliminaries about decisions
Dec : (P : Set) -> Set
Dec P = (P -> Zero) + P

-- what is it to be a Decided Set ?
record Decided : Set1 where
  constructor _?!_
  field
    Question : Set
    answer : Dec Question
infix 9 _?!_
open Decided

infixr 5 _&D_
_&D_ : Decided -> Decided -> Decided
(Qa ?! _ &D Qb ?! _) .Question = Qa * Qb
(_ ?! `0 , pa &D _ ?! bp , pb) .answer = `0 , fst - pa
(_ ?! `1 , pa &D _ ?! `0 , pb) .answer = `0 , snd - pb
(_ ?! `1 , pa &D _ ?! `1 , pb) .answer = `1 , pa , pb

D1 : Decided
D1 .Question = One
D1 .answer = `1 , <>

D0 : Decided
D0 .Question = Zero
D0 .answer = `0 , id

decEnum : (ls : List String) -> (<: _-in ls :> -> Decided) -> Decided
decEnum [] el = D1
decEnum (x ,- ls) el = el zee &D decEnum ls (suu - el)

decTab : (S : UF) -> (T : ElF S -> Decided) -> Decided
decTab (R `>< S) T = decTab R \r -> decTab (S r) \ s -> T (r , s)
decTab `0 T = D1
decTab `1 T = T <>
decTab (`E x) T = decEnum x T

notD : Decided -> Decided
notD (Q ?! _) .Question = Q -> Zero
notD (_ ?! `0 , p) .answer = `1 , p
notD (_ ?! `1 , p) .answer = `0 , \ q -> q p

-- Universe of Decidable Propositions
data UD : Set where
  -- Conjunction
  -- not strictly needed, but using `#>> would make things unreadable
  _`&_ : UD -> UD -> UD

  -- false and true
  `0 `1 : UD

  -- let's have not.
  `not : UD -> UD

  -- Tabulated functions -- domain in UF
  -- (could we get away with functions?)
  _`#>>_ : (S : UF) -> (T : ElF S -> UD) -> UD

DecideUD : UD -> Decided
DecideUD (D `& E) = DecideUD D &D DecideUD E
DecideUD `0 = D0
DecideUD `1 = D1
DecideUD (`not D) = notD (DecideUD D)
DecideUD (S `#>> T) = decTab S \s -> DecideUD (T s)

ElD : UD -> Set
ElD = DecideUD - Question

-- Since we've got classical logic (essentially) in our hands...
_`||D_ : UD -> UD -> UD
D `||D E = `not (`not D `& `not E)

-- Ought to show we can decide (ElD D) + (ElD E)
Decide+ : (D E : UD) -> ElD (D `||D E) -> (ElD D) + (ElD E)
Decide+ D E w with DecideUD D .answer | DecideUD E .answer
... | `0 , pd | `0 , pe with () <- w (pd , pe)
... | `0 , pd | `1 , pe = `1 , pe
... | `1 , pd | be , pe = `0 , pd

-- Finitary existential
_`#><_ : (S : UF) -> (T : ElF S -> UD) -> UD
S `#>< T = `not (S `#>> \ s -> `not (T s))

-- Decide enums
WitnessEnum : (ls : List String) (T : ElF (`E ls) -> UD) -> ElD ((`E ls) `#>< T) -> ElF (`E ls) >< (\ s -> ElD (T s))
WitnessEnum [] T w with () <- w <>
WitnessEnum (x ,- xs) T w with DecideUD (T zee) .answer
... | `1 , p = zee , p
... | `0 , p with WitnessEnum xs (suu - T) ((p ,_) - w)
... | y , q = suu y , q

-- We can still get a witness out of that!
WitnessEx : (S : UF) -> (T : ElF S -> UD) -> ElD (S `#>< T) -> ElF S >< (\ s -> ElD (T s))
WitnessEx (R `>< S) T ex with decTab R (\ r -> notD (DecideUD (S r `#>< \ s -> (T (r , s))))) .answer
  -- with (r , st) <- WitnessEx R (\ r -> (S r) `#>< (\ s -> T (r , s))) {!!}
... | `1 , p = {!!} -- to make progress here, we need double-negation elimination
... | `0 , p with WitnessEx R (\ r -> (S r) `#>< (\ s -> T (r , s))) p
... | (r , st) with decTab (S r) (λ s → notD (DecideUD (T (r , s)))) .answer
... | `0 , q with (s , t) <- WitnessEx (S r) (\ s -> T (r , s)) q = (r , s) , t
... | `1 , q with () <- st q
WitnessEx `0 T ex with () <- ex <>
WitnessEx `1 T ex with DecideUD (T <>) .answer
... | `0 , p with () <- ex p
... | `1 , p = <> , p
WitnessEx (`E x) T ex = WitnessEnum x T ex

{-
HERE

This was an attempt to introduce a universe of decided types.

4. The plan, then, is to show that Equality for U Data lives in UD.

-}
-}
