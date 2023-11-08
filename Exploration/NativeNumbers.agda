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
naughtE : forall {l}{X : Set l} -> Zero -> X
naughtE (hide ())
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

rw<N : (a b c d : Nat) -> a ~ b -> c ~ d -> a <N c -> b <N d
rw<N a b c d r~ r~ p = p

Fin : Nat -> Set
Fin n = < _<N n >

slacken : (s d : Nat) -> s <N (su s +N d)
slacken ze d = _
slacken (su s) d = slacken s d

tooBig : (n m : Nat) -> (n +N m) <N n -> Zero
tooBig (su n) m l = tooBig n m l

finEqNum : (n : Nat)(x y : Fin n) -> fst x ~ fst y -> x ~ y
finEqNum (su n) (ze , <>) (.ze , <>) r~ = r~
finEqNum (su n) (su x , lx) (.(su x) , ly) r~
  = (\ (x , p) -> (su x , p)) $~ finEqNum n (x , lx) (x , ly) r~

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
  mod-su n m                        -- knock off 1 more and reset
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
mod-su-stop n k d ze (s , p , q) = ze , r~ ,
  rw<N s k (su (s +N d)) (su n)
    (s < s +N0 ]~ s +N ze ~[ q > k [QED])
    (su $~ p)
    (slacken s d)
 -- rewrite s +N0 = ze , r~ , slacken s d
mod-su-stop n k ze (su m) (s , pp , qq) =
  let (q , p , l) = mod-su-stop n m n m (ze , r~ , r~) in
   su q ,
   (((su n +N (q *N su n)) +N mod-su-worker n m n m) ~[ assoc+N (su n) _ _ >
   (su n +N ((q *N su n) +N mod-su-worker n m n m))  ~[ (su n +N_) $~ p >
   su (n +N m)                                       < n +Nsu m ]~
   n +N su m                                         < _+N su m $~ pp ]~
   (s +N ze) +N su m                                 ~[ _+N su m $~ (s +N0) >
   s +N su m                                         ~[ qq >
   k [QED]) ,
   l
{-
mod-su-stop n k ze (su m) (s , r~ , r~)
  with (q , p , l) <- mod-su-stop n m n m (ze , r~ , r~)
  rewrite s +N0
     = su q
     , (((su s +N (q *N su s)) +N mod-su-worker s m s m) ~[ assoc+N (su s) _ _ >
        (su s +N ((q *N su s) +N mod-su-worker s m s m)) ~[ (su s +N_) $~ p >
        (su s +N m) < s +Nsu m ]~
        (s +N su m) [QED])
     , l
-}
mod-su-stop n k (su d) (su m) (s , p , q) = mod-su-stop n k d m
  (su s ,
   (su (s +N d)  < s +Nsu d ]~
   s +N su d     ~[ p >
   n             [QED]) ,
   (su s +N m    < s +Nsu m ]~
   s +N su m     ~[ q >
   k             [QED])
   )

mod-su-good : (n m r : Nat) ->  r ~ mod-su n m ->
     Nat >< \ q -> (((q *N su n) +N r) ~ m) * (r <N su n)
mod-su-good n m r p = 
  let (k , q , s ) = mod-su-stop n m n m (mod-su-start n m) in
  k ,
  ((( k *N su n) +N r)          ~[ (k *N su n) +N_ $~ p >
   (( k *N su n) +N mod-su n m) ~[ q >
   m                            [QED]) ,
  rw<N (mod-su n m) r _ (su n) (sym p) r~ s
  -- mod-su-stop n m n m (mod-su-start n m)

div-mod-su-good : (n m : Nat) ->
  Nat >< \ q -> Nat >< \ r ->
  (((q *N su n) +N r) ~ m) * (r <N su n)
div-mod-su-good n m
  with r <- mod-su n m
     | q , g <- mod-su-good n m _ r~
     = q , r , g

mod-su-already : (n : Nat)(y : Fin (su n))(q : Nat)(r : Nat) ->
  (((q *N su n) +N r) ~ fst y) -> (r <N su n) -> (q ~ ze) * (r ~ fst y)
mod-su-already n y ze r e rl = r~ , e
mod-su-already n (m , ml) (su q) r e rl =
  naughtE (tooBig (su n) ((q *N su n) +N r)
    (rw<N m (su n +N ((q *N su n) +N r)) (su n) _
      (m < e ]~
       ((su n +N (q *N su n)) +N r) ~[ assoc+N (su n) _ _ >
       (su n +N ((q *N su n) +N r)) [QED])
     r~ ml))

-----------------------------------------------------------------------

module _ {n : Nat} where

  private M = Fin (su n)

  reduce : Nat -> M
  reduce x
    with _ , r , _ , l <- div-mod-su-good n x
       = r , l

  zeF : M
  zeF = reduce 0

  _+F_ : M -> M -> M
  (x , _) +F (y , _) = reduce (x +N y)

  wannaHom : (x y : Nat) -> fst (reduce x +F reduce y) ~ fst (reduce (x +N y))
  wannaHom x y
    with rx <- mod-su n x | qx , ex , lx <- mod-su-good n x _ r~
    with ry <- mod-su n y | qy , ey , ly <- mod-su-good n y _ r~
           = {!!}

{-
  define <F as <N on fst
  suppose x : Nat and y : Fin (su n)

  x <N fst y
   <=>
  reduce x <F y
-}


  zeF+F : (y : M) -> (zeF +F y) ~ y
  zeF+F (y , l) = {!wannaHom ze y!}
  {-
  zeF+F (y , l)
    -- grr with div-mod-su-good doesn't get abstracted
    with mod-su-worker n y n y
       | mod-su-stop n y n y (0 , r~ , r~)
  ... | r | q , e , l' 
       = finEqNum (su n) (r , l') (y , l) (snd (mod-su-already n (y , l) q r e l'))
  -}
