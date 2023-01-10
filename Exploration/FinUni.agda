module FinUni where

data _~_ {X : Set}(x : X) : X -> Set where
  r~ : x ~ x


data Zero : Set where
record One : Set where constructor <>
data Two : Set where `0 `1 : Two
record _><_ (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open _><_ public
infixr 10 _,_
_+_ : Set -> Set -> Set
S + T = Two >< \ { `0 -> S ; `1 -> T }

module _ {X : Set} where
  <_> : (T : X -> Set) -> Set
  < T > = X >< T
  _*:_ : (X -> Set) -> (X -> Set) -> (X -> Set)
  (F *: G) x = F x >< \ _ -> G x
  infix 10 _*:_
  infix 5 <_>

data UF : Set
ElF : UF -> Set

data UF where
  zero one two : UF
  sg : (S : UF)(T : ElF S -> UF) -> UF

ElF zero     = Zero
ElF one      = One
ElF two      = Two
ElF (sg S T) = ElF S >< \ s -> ElF (T s)

_`+_ : UF -> UF -> UF
S `+ T = sg two \ { `0 -> S ; `1 -> T }

PI : (S : UF)(R : ElF S -> Set) -> Set
PI zero R = One
PI one R = R <>
PI two R = R `0 >< \ _ -> R `1
PI (sg S T) R = PI S \ s -> PI (T s) \ t -> R (s , t)

pi : (S : UF)(R : ElF S -> UF) -> UF
pi zero     R = one
pi one      R = R <>
pi two      R = sg (R `0) \ _ -> R `1
pi (sg S T) R = pi S \ s -> pi (T s) \ t -> R (s , t)

-- morally, ElF (pi S R) = PI S \ s -> ElF (R s)

lam : (S : UF)(R : ElF S -> UF)
   -> ((s : ElF S) -> ElF (R s))
   -> ElF (pi S R)
lam zero R f = <>
lam one R f = f <>
lam two R f = f `0 , f `1
lam (sg S T) R f =
  lam S (\ s -> pi (T s) \ t -> R (s , t)) \ s ->
  lam (T s) (\ t -> R (s , t)) \ t ->
  f (s , t)

app : (S : UF)(R : ElF S -> UF)
   -> ElF (pi S R)
   -> ((s : ElF S) -> ElF (R s))
app one R r <> = r
app two R (f0 , f1) `0 = f0
app two R (f0 , f1) `1 = f1
app (sg S T) R f (s , t) = 
  app (T s) (\ t -> R (s , t))
    (app S (\ s -> pi (T s) \ t -> R (s , t)) f s)
    t

_-_  : (T : UF)(t : ElF T) -> UF
miss : (T : UF)(t : ElF T)(u : ElF (T - t)) -> ElF T
one - <> = zero
two - t = one
sg S T - (s , t) =
  (sg (S - s) \ u -> T (miss S s u)) `+ (T s - t)
miss two `0 <> = `1
miss two `1 <> = `0
miss (sg S T) (s , t) (`0 , u , t') = miss S s u , t'
miss (sg S T) (s , t) (`1     , u ) = s , miss (T s) t u

eq? : (T : UF)(t t' : ElF T)
   -> (ElF (T - t) >< \ u -> t' ~ miss T t u)
   +  (t' ~ t)
eq? one <> <> = `1 , r~
eq? two `0 `0 = `1 , r~
eq? two `0 `1 = `0 , <> , r~
eq? two `1 `0 = `0 , <> , r~
eq? two `1 `1 = `1 , r~
eq? (sg S T) (s , t) (s' , t') with eq? S s s'
... | `0 , u , r~ = `0 , (`0 , u , t') , r~
... | `1 , r~ with eq? (T s) t t'
... | `0 , u , r~ = `0 , (`1 , u) , r~
... | `1 , r~ = `1 , r~

record Fam (X : Set) : Set1 where
  constructor _//_
  field
    Ix : Set
    im : Ix -> X
open Fam public

module _ {X : Set} where

  [_/_!_] : (T : UF) -> (ElF T -> X -> Fam X) -> X -> Fam X
  [ zero / [_!_] ! x ] = One // \ _ -> x
  [ one / [_!_] ! x ]  = [ <> ! x ]
  [ two / [_!_] ! x ]  =
    let F0 = [ `0 ! x ] in
      (Ix F0 >< \ f0 -> Ix [ `1 ! im F0 f0 ]) //
      \ (f0 , f1) -> im [ `1 ! im F0 f0 ] f1
  [ sg S T / [_!_] ! x ] =
    [ S / (\ s -> [ T s / (\ t -> [ s , t !_]) !_]) ! x ]

Iso : UF -> UF -> Set
Iso S T = Ix F >< \ U -> ElF (im F U) -> Zero
  where
    F = [ S / (\ _ X -> ElF X // (X -_)) ! T ]

