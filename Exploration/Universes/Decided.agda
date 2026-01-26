module Decided where

open import String

open import Basics
open import Thinnings
open import Membership
open import Finite
open import TabulatedFunctions

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
