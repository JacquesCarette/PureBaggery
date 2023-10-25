module NativeNumbers where

data _~_ {X : Set}(x : X) : X -> Set where
  r~ : x ~ x
{-# BUILTIN EQUALITY _~_ #-}

module _ {X : Set}(x : X) where

  _~[_>_ : forall {y z} -> x ~ y -> y ~ z -> x ~ z
  _~[_>_ r~ q = q
  _<_]~_ : forall {y z} -> y ~ x -> y ~ z -> x ~ z
  _<_]~_ r~ q = q
  _[QED] : x ~ x
  _[QED] = r~

  infixr 2 _~[_>_ _<_]~_
  infix 3 _[QED]

module _ {X : Set}{x y : X}(q : x ~ y) where
  sym : y ~ x
  sym = y < q ]~ x [QED]

_$~_ : forall {S T}(f : S -> T){x y : S} -> x ~ y -> f x ~ f y
f $~ r~ = r~
_~$~_ : forall {S T}{f g : S -> T} -> f ~ g -> {x y : S} -> x ~ y -> f x ~ f y
r~ ~$~ r~ = r~
infixl 4 _$~_ _~$~_


--------------------------------------------------------------------
-- First, a lot of kit to get started

-- Using proof irrelevance keeps us from using details that we
-- should not care about. [Also brings in complications.]
record Hide (X : Set) : Set where
  constructor hide
  field
    .expose : X
open Hide public

--------------
-- empty, singleton and (exactly) 2 point set along with eliminator
data Zero' : Set where
Zero = Hide Zero'
record One : Set where constructor <>
data Two : Set where `0 `1 : Two
_<01>_ : forall {k}{P : Two -> Set k} -> P `0 -> P `1 -> (b : Two) -> P b
(p0 <01> p1) `0 = p0
(p0 <01> p1) `1 = p1

-- dependent sum, disjoint union (coproduct) and product
record _><_ (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open _><_ public
infixr 10 _,_
_+_ _*_ : Set -> Set -> Set
S + T = Two >< \ { `0 -> S ; `1 -> T }
S * T = S >< \ _ -> T

module _ {I : Set} where
  _*:_ _-:>_ : (I -> Set) -> (I -> Set) -> (I -> Set)
  (P *: Q) i = P i * Q i
  (P -:> Q) i = P i -> Q i
  [_] <_> : (I -> Set) -> Set
  [ P ] = forall {i} -> P i
  < P > = _ >< P

data Nat : Set where
  ze : Nat
  su : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

_+N_ : Nat -> Nat -> Nat
ze +N y = y
su x +N y = su (x +N y)

_+N0 : (n : Nat) -> (n +N 0) ~ n
ze +N0 = r~
su n +N0 = su $~ (n +N0)

_+Nsu_ : (n m : Nat) -> (n +N su m) ~ su (n +N m)
ze +Nsu m = r~
su n +Nsu m = su $~ (n +Nsu m)

assoc+N : (x y z : Nat) -> ((x +N y) +N z) ~ (x +N (y +N z))
assoc+N ze y z = r~
assoc+N (su x) y z = su $~ assoc+N x y z

_*N_ : Nat -> Nat -> Nat
ze *N y = ze
su x *N y = y +N (x *N y)

_<N_ : Nat -> Nat -> Set
x <N ze = Zero
ze <N su y = One
su x <N su y = x <N y

Fin : Nat -> Set
Fin n = < _<N n >

slacken : (s d : Nat) -> s <N (su s +N d)
slacken ze d = _
slacken (su s) d = slacken s d

---------------------------------------------------------------

mod-su
   : Nat  -- n, for reduction modulo (su n)
  -> Nat  -- what is to be reduced
  -> Nat  -- the result

mod-su-worker
   : Nat  -- master copy of n
  -> Nat  -- current candidate for the output
  -> Nat  -- how much of su n we have left to subtract, *less 1*
  -> Nat  -- how much is left of the candidate
  -> Nat
mod-su-worker n k     d   ze    = k -- can't subtract? candidate's good!
mod-su-worker n k  ze    (su m) =   -- subtracted n already?
  mod-su-worker n m n m             -- knock off 1 more and reset
mod-su-worker n k (su d) (su m) =   -- potato potato
  mod-su-worker n k d m

mod-su n m = mod-su-worker n m n m

Mod-Su-Worker-Invariant : Nat -> Nat -> Nat -> Nat -> Set
Mod-Su-Worker-Invariant n k d m = 
  Nat >< \ s -> ((s +N d) ~ n) * ((s +N m) ~ k)

mod-su-start : (n m : Nat) -> Mod-Su-Worker-Invariant n m n m
mod-su-start n m = ze , r~ , r~

mod-su-stop : (n k d m : Nat)
  -> Mod-Su-Worker-Invariant n k d m
  -> let r = mod-su-worker n k d m in
     Nat >< \ q -> (((q *N su n) +N r) ~ k) * (r <N su n)
mod-su-stop n k d ze (s , r~ , r~) rewrite s +N0 = ze , r~ , slacken s d
mod-su-stop n k ze (su m) (s , r~ , r~)
  with (q , p , l) <- mod-su-stop n m n m (ze , r~ , r~)
  rewrite s +N0
     = su q
     , (((su s +N (q *N su s)) +N mod-su-worker s m s m) ~[ assoc+N (su s) _ _ >
        (su s +N ((q *N su s) +N mod-su-worker s m s m)) ~[ (su s +N_) $~ p >
        (su s +N m) < s +Nsu m ]~
        (s +N su m) [QED])
     , l
mod-su-stop n k (su d) (su m) (s , r~ , r~) = mod-su-stop n k d m
  (su s , sym (s +Nsu d) , sym (s +Nsu m))

mod-su-good : (n m r : Nat) ->  r ~ mod-su n m ->
     Nat >< \ q -> (((q *N su n) +N r) ~ m) * (r <N su n)
mod-su-good n m _ r~ = mod-su-stop n m n m {!mod-su-start n m!}
