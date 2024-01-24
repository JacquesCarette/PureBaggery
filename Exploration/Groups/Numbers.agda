module Numbers where

-- needs refactored in terms of call graphs?

open import Basics
open import ExtUni
open import Reasoning
open import Group
open import Hom

{- -- in Basics.agda
-- Nat is useful for non-trivial examples
data Nat : Set where ze : Nat ; su : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}
-}

-- SYmmetric Difference
syd : Nat -> Nat -> Nat
syd ze      y     = y
syd (su x)  ze    = su x
syd (su x) (su y) = syd x y

syd-sym : (x y : Nat) -> Pr (Oq `Nat (syd x y) (syd y x))
syd-sym ze ze = _
syd-sym ze (su y) = refl `Nat (su y)
syd-sym (su x) ze = refl `Nat (su x)
syd-sym (su x) (su y) = syd-sym x y

syd-ze : (x : Nat) -> Pr (Oq `Nat (syd x x) ze)
syd-ze ze     = <> 
syd-ze (su x) = syd-ze x

_+N_ : Nat -> Nat -> Nat
ze +N y = y
su x +N y = su (x +N y)

syd+N : (x y z : Nat) -> Pr (Oq `Nat z (x +N y) `=> Oq `Nat (syd x z) y)
syd+N ze y z p = p
syd+N (su x) y (su z) p = syd+N x y z p

module _ where
  open Monoid
  
  Monoid+N : Monoid `Nat
  neu Monoid+N = ze
  mul Monoid+N = _+N_
  mulneu- Monoid+N x = refl `Nat x
  mul-neu Monoid+N ze = <>
  mul-neu Monoid+N (su x) = mul-neu Monoid+N x
  mulmul- Monoid+N ze y z = refl `Nat (y +N z)
  mulmul- Monoid+N (su x) y z = mulmul- Monoid+N x y z

  module _ {X : U}(MX : Monoid X) where
    private
      module MA = Monoid Monoid+N
      module MX = Monoid MX
    open EQPRF X

    _-times_ :  El (`Nat `> X `> X)
    ze -times x = MX.neu
    su n -times x = MX.mul x (n -times x)

    open HomMonoid
    homFromMonoid+N : El X -> HomMonoid Monoid+N MX
    hom (homFromMonoid+N x) n = n -times x
    homneu (homFromMonoid+N x) = refl X MX.neu
    hommul (homFromMonoid+N x) ze b = 
      (b -times x) < MX.mulneu- (b -times x) ]-
      MX.mul MX.neu (b -times x) [QED]
    hommul (homFromMonoid+N x) (su a) b = 
      MX.mul x ((a +N b) -times x) -[ cong (MX.mul x) (hommul (homFromMonoid+N x) a b) >
      MX.mul x (MX.mul (a -times x) (b -times x)) < MX.mulmul- x (a -times x) (b -times x) ]-
      MX.mul (MX.mul x (a -times x)) (b -times x) [QED]

    onlyHomFromMonoid+N : (h : HomMonoid Monoid+N MX)
      -> Pr (Oq (`Nat `> X) (hom h) (_-times (hom h 1)))
    onlyHomFromMonoid+N h = homogTac (`Nat `> X) (hom h) (_-times (hom h 1)) help where
      help : (n : Nat) -> Pr (Oq X (hom h n) (n -times hom h 1))
      help ze = homneu h
      help (su n) = 
        hom h (su n) -[ hommul h 1 n >
        MX.mul (hom h 1) (hom h n) -[ cong (MX.mul (hom h 1)) (help n) >
        MX.mul (hom h 1) (n -times hom h 1) [QED]

mulHom : Nat -> HomMonoid Monoid+N Monoid+N
mulHom x = homFromMonoid+N Monoid+N x

_*N_ : Nat -> Nat -> Nat
n *N x = HomMonoid.hom (mulHom x) n

_-dividesU_ : Nat -> Nat -> U
n -dividesU m = `Nat `>< \ q -> `Pr (Oq `Nat m (q *N n))
_-divides_ : Nat -> Nat -> P
n -divides m = `In (n -dividesU m)

trichotomy : (x y : Nat)(M : Nat -> Nat -> Nat -> U)
  -> ((a d : Nat) -> El (M a (a +N su d) (su d)))
  -> ((n : Nat) -> El (M n n ze))
  -> ((a d : Nat) -> El (M (a +N su d) a (su d)))
  -> El (M x y (syd x y))
trichotomy ze ze M l e g = e ze
trichotomy ze (su y) M l e g = l ze y
trichotomy (su x) ze M l e g = g ze x
trichotomy (su x) (su y) M l e g = trichotomy x y (\ x y z -> M (su x) (su y) z)
  (su - l)
  (su - e)
  (su - g)

module _ where

  open EQPRF `Nat
  open Monoid Monoid+N

  syd-chop : (a b c d : Nat) -> Pr (Oq `Nat (a +N b) (c +N d) `=> Oq `Nat (syd a c) (syd b d))
  syd-chop ze b ze d q = trans ze (syd b b) (syd b d) (!_{syd b b}{ze} (syd-ze b)) (cong (syd b) q)
  syd-chop ze b (su c) d q = trans (su c) (syd (su c +N d) d) (syd b d)
    {!syd+N d (su c) (su c +N d)!}
    (cong {su c +N d}{b} (\ x -> syd x d) (!_{b}{su c +N d} q))
  syd-chop (su a) b ze d q = {!!}
  syd-chop (su a) b (su c) d q = syd-chop a b c d q

  syd-mid : (x y z : Nat)(M : Nat -> U) -> El (
    M (syd x y +N syd y z)
    `> M (syd (syd x y) (syd y z))
    `> M (syd x z))
  syd-mid x y z M = trichotomy x y (\ x y xy -> M (xy +N syd y z) `>  M (syd xy (syd y z)) `> M (syd x z))
    (\ x xy -> trichotomy (x +N su xy) z
    -- up then
      (\ a z d -> `Pr (Oq `Nat a (x +N su xy)) `> M (su (xy +N d)) `> M (syd (su xy) d) `> M (syd x z))
      -- up more
      (\ n d q m _ -> subst `Nat (!_{syd x (n +N su d)}{su (xy +N su d)}
        (syd+N x (su xy +N su d) (n +N su d)
          (trans (n +N su d) ((x +N su xy) +N su d) (x +N su (xy +N su d))
            (cong{n}{x +N su xy} (_+N su d) q)
            (mulmul- x (su xy) (su d))))
        ) M m)
      -- along
      (\ n q a b -> subst `Nat (!_ {syd x n}{su xy} (syd+N x (su xy) n q)) M b)
      -- down
      (\ n d q _ m -> {!!})

      (refl `Nat (x +N su xy)))
    -- along
    (\ _ _ m -> m)
    {!!}

module _ (n : Nat) where

  open EQPRF `Nat
  open Monoid Monoid+N
  open HomMonoid (mulHom n)

  private
    addLem : (a b : Nat) -> El
      (n -dividesU a `> n -dividesU b `> n -dividesU (a +N b))
    addLem a b (qa , pa) (qb , pb) = qa +N qb , (
      (a +N b) -[ refl (`Nat `> `Nat `> `Nat) _+N_ a (qa *N n) pa b (qb *N n) pb >
      _<_]-_ {(qa +N qb) *N n} ((qa *N n) +N (qb *N n)) (hommul qa qb)
      (refl `Nat ((qa +N qb) *N n)))

  `Mod : U
  `Mod = `Quotient `Nat (\ x y -> n -divides (syd x y))
    (record
      { eqR = \ x -> hide (ze , syd-ze x)
      ; eqS = \ x y (hide h) -> hide (fst h , (
         syd y x -[ syd-sym y x >
         syd x y -[ snd h >
         (fst h *N n) [QED]))
      ; eqT = \ x y z (hide xy) (hide yz) ->
          syd-mid x y z (\ w -> `Pr (`In (`Nat `>< (\ s -> `Pr (Oq `Nat w (s *N n))))))
            (hide (addLem (syd x y) (syd y z) xy yz))
            {!!}
      })

{- -- sadly, we must make do with the P version of this thing
data [_+N_]~_ : Nat -> Nat -> Nat -> Set where
  ze : forall {y} ->                      [ ze   +N y ]~ y
  su : forall {x y z} -> [ x +N y ]~ z -> [ su x +N y ]~ su z
-}

{-
-- if we don't get nice inversion via pattern matching, is it worth it?
[_+N_]~_ : Nat -> Nat -> Nat -> P
[ ze   +N y ]~ z    = Eq `Nat `Nat y z
[ su x +N y ]~ ze   = `Zero
[ su x +N y ]~ su z = [ x +N y ]~ z

-- but functional induction is worth it, one way or another
ind+N : (x y z : Nat)(p : Pr ([ x +N y ]~ z))
     -> (M : Nat -> Nat -> Nat -> U)
     -> (mze : {y : Nat} -> El (M ze y y))
     -> (msu : {x y z : Nat} -> El (M x y z) -> El (M (su x) y (su z)))
     -> El (M x y z)
ind+N ze y z p M mze _ = J `Nat {y}{z} p (\ z _ -> M ze y z) mze
ind+N (su x) y (su z) p M mze msu = msu (ind+N x y z p M mze msu)
-}

-- derive "relation induction", i.e., the eliminator for the above inductive presentation?

-- the following gadgetry is more or less what's needed to generate a
-- small category internal to U, with a composition relation in P

{-
module _ where

  private
    T : Nat -> Nat -> U
    T x y = `Nat `>< \ z -> `Pr ([ x +N y ]~ z)
  
  add : forall x y -> El (T x y)
  add  ze    y = y , refl `Nat y
  add (su x) y = (su >><< id) (add x y)

  addUniq : (x y : Nat)(a b : El (T x y)) -> Pr (Eq (T x y) (T x y) a b)
  addUniq x y (a , p) = ind+N x y a p
    (\ x y z -> T x y `-> \ (b , _) -> `Pr (Eq `Nat `Nat z b `/\ `One))
    (\ (z , q) -> q , <>)
    (\ { h (su w , q) -> h (w , q) })

_+N_ : El (`Nat `> `Nat `> `Nat)
x +N y = fst (add x y)

-- is this all we need?
ind+N' : (x y : Nat)
     -> (M : Nat -> Nat -> Nat -> U)
     -> (mze : {y : Nat} -> El (M ze y y))
     -> (msu : {x y z : Nat} -> El (M x y z) -> El (M (su x) y (su z)))
     -> El (M x y (x +N y))
ind+N' ze y M mze _ = mze --  J `Nat {y}{z} p (\ z _ -> M ze y z) mze
ind+N' (su x) y M mze msu = msu (ind+N' x y M mze msu)


ze+N_ : (n : Nat) -> Pr ([ ze +N n ]~ n)
ze+N n = refl `Nat n

_+Nze : (n : Nat) -> Pr ([ n +N ze ]~ n)
ze +Nze = _
su n +Nze = n +Nze

module _ where
  private
    M : Nat -> Nat -> Nat -> U
    M n01 n12 n02 =
     `Nat `-> \ n13 -> `Nat `-> \ n23 -> `Pr ([ n12 +N n23 ]~ n13) `>
     (`Nat `>< \ n03 -> `Pr ([ n01 +N n13 ]~ n03 `/\ [ n02 +N n23 ]~ n03))
  assoc+N03 : (n01 n12 n02 : Nat) -> Pr ([ n01 +N n12 ]~ n02) -> El (M n01 n12 n02)
  assoc+N03 n01 n12 n02 v = ind+N n01 n12 n02 v M
    (\ n13 n23 w -> n13 , refl `Nat n13 , w)
    (\ h n13 n23 w -> (su >><< id) (h n13 n23 w))


_<N_ : Nat -> Nat -> P
x    <N ze = `Zero
ze   <N su z = `One
su x <N su z = x <N z

n<Nsun : (n : Nat) -> Pr (n <N su n)
n<Nsun ze = _
n<Nsun (su n) = n<Nsun n

trans<N : (i j k : Nat) -> Pr (i <N j) -> Pr (j <N k) -> Pr (i <N k)
trans<N ze (su j) (su k) p q = _
trans<N (su i) (su j) (su k) p q = trans<N i j k p q

Fin : Nat -> U
Fin n = `Nat `>< \ k -> `Pr (k <N n)

tooBig<N : (n e : Nat) -> Pr ((n +N e) <N n) -> Zero
tooBig<N (su n) e l = tooBig<N n e l

[_*N_]~_ : Nat -> Nat -> Nat -> P
[ ze   *N y ]~ ze   = `One
[ ze   *N y ]~ su _ = `Zero
[ su x *N y ]~ z    = `In (`Nat `>< \ xy -> `Pr (([ x *N y ]~ xy) `/\ ([ y +N xy ]~ z)))

module _ where

  private
    T : Nat -> Nat -> U
    T x y = `Nat `>< \ z -> `Pr ([ x *N y ]~ z)
  
  mul : forall x y -> El (T x y)
  mul ze y = ze , _
  mul (su x) y
    with xy , h <- mul x y
    with z , p <- add y xy
       = z , hide (xy , h , p)

  mulUniq : (x y : Nat)(a b : El (T x y)) -> Pr (Eq (T x y) (T x y) a b)
  mulUniq ze y (ze , p) (ze , q) = _
  mulUniq (su x) y (a , hide p) (b , hide q)
    with xy , h <- mul x y
       = {!!}

-- but functional induction is worth it, one way or another
ind*N : (x y z : Nat)(p : Pr ([ x *N y ]~ z))
     -> (M : Nat -> Nat -> Nat -> U)
     -> (mze : {y : Nat} -> El (M ze y ze))
     -> (msu : {x y xy z : Nat} -> El (M x y xy) -> Pr ([ y +N xy ]~ z) -> El (M (su x) y z))
     -> El (M x y z)
ind*N ze y ze p M mze msu = mze
ind*N (su x) y z (hide p) M mze msu
  with xy , h <- mul x y
  with z' , q <- add y xy
     = msu (ind*N x y xy h M mze msu) {!!}



-- a little extra never hurt anybody
-- mulAdd n x s = n * x + s
mulAdd : Nat -> Nat -> Nat -> Nat
mulAdd ze     x s = s
mulAdd (su n) x s = x +N mulAdd n x s

_*N_ : Nat -> Nat -> Nat
x *N y = mulAdd x y ze
-}
{-
-- subtraction as a view
data InFin? (n : Nat) : Nat -> Set where
  inFin : (k : El (Fin n)) -> InFin? n (fst k)
  tooBigBy : (e : Nat) -> InFin? n (n +N e)

inFin? : (n m : Nat) -> InFin? n m
inFin? ze m          = tooBigBy m
inFin? (su n) ze     = inFin (ze , _)
inFin? (su n) (su m) with inFin? n m
inFin? (su n) (su .k) | inFin (k , kp) = inFin (su k , kp)
inFin? (su n) (su .(n +N e)) | tooBigBy e = tooBigBy e

substNatEq : (x y : Nat)(q : Pr (Eq `Nat `Nat x y))(P : Nat -> Set)
  -> P x -> P y
substNatEq ze ze q P px = px
substNatEq (su x) (su y) q P px = substNatEq x y q (su - P) px

data UnPlus (n : Nat) : Set where
  split+ : ((a b : Nat) -> Pr (Eq `Nat `Nat n (su a +N b)) -> UnPlus b) -> UnPlus n

unPlus : (n : Nat) -> UnPlus n
unPlus ze = split+ \ _ _ ()
unPlus (su n) with unPlus n
... | res@(split+ unp) = split+ \
  { ze b pf     -> substNatEq n b pf UnPlus res
  ; (su a) b pf -> unp a b pf
  }

data DivMod : Nat -> Nat -> Set where
  divBy0 : (n : Nat) -> DivMod n ze
  quotRem : {d : Nat}(q : Nat)(r : El (Fin d)) -> DivMod (mulAdd q d (fst r)) d

{-
data DivModR : (n d : Nat) -> DivMod n d -> Set where
  divModRd0 : {n : Nat} -> DivModR n ze (divBy0 n)
  divModStop : {d : Nat}{r@(k , _) : El (Fin (su d))} -> DivModR k (su d) (quotRem ze r)
  divModStep : {q d n m : Nat}{r@(k , _) : El (Fin (su d))}
    -> DivModR n (su d) (quotRem q r)
    -> Pr (Eq `Nat `Nat (su d +N n) m)
    -> DivModR m (su d) (quotRem (su q) r)
-}

divMod' : (n d : Nat) -> UnPlus n -> DivMod n d
divMod' n ze r = divBy0 n
divMod' n (su d) r with inFin? (su d) n
divMod' .(fst k) (su d) r | inFin k = quotRem ze k
divMod' .(su d +N e) (su d) (split+ f) | tooBigBy e with divMod' e (su d) (f d e (refl `Nat (d +N e)))
divMod' .(su d +N (mulAdd q (su d) (fst r))) (su d) (split+ f) | tooBigBy ._ | quotRem q r
  = quotRem (su q) r

divMod : (n d : Nat) -> DivMod n d
divMod n d = divMod' n d (unPlus n)

reduce : (n : Nat) -> Nat -> El (Fin (su n))
reduce n k with divMod k (su n)
reduce n .(mulAdd q (su n) (fst r)) | quotRem q r = r

{-
reducePlus : (n x : Nat) -> Pr (Eq (Fin (su n)) (Fin (su n))
  (reduce n (su n +N x)) (reduce n x))
reducePlus n x with inFin? n (n +N x)
... | z = {!!}

reduceMulAdd : (q n r : Nat) -> Pr (
  Eq (Fin (su n)) (Fin (su n))
    (reduce n (mulAdd q (su n) r)) (reduce n r))
reduceMulAdd ze n r = refl (Fin (su n)) (reduce n r)
reduceMulAdd (su q) n r = (_, <>) let open EQPRF `Nat in
  fst (reduce n (su n +N mulAdd q (su n) r)) -[ fst (reducePlus n (mulAdd q (su n) r)) >
  fst (reduce n (mulAdd q (su n) r)) -[ fst (reduceMulAdd q n r) >
  fst (reduce n r) [QED]
-}

finZero : (n : Nat) -> El (Fin (su n))
finZero n = 0 , _

finPlus : (n : Nat) -> El (Fin (su n) `> Fin (su n) `> Fin (su n))
finPlus n (x , _) (y , _) = reduce n (x +N y)

plusInverse : (n : Nat) -> El (Fin (su n)) -> El (Fin (su n))
plusInverse n (ze , p) = n , n<sun n
plusInverse (su n) (su i , p) with j , q <- plusInverse n (i , p)
  = j , trans< j (su n) (su (su n)) q (n<sun (su n))

plusAbsorbZero : (n : Nat)(x : El (Fin (su n))) ->
  Pr (Eq (Fin (su n)) (Fin (su n))(finPlus n (finZero n) x) x)
plusAbsorbZero n (x , p) with inFin? (su n) x
... | inFin (k , _) = refl `Nat k , _
... | tooBigBy e with () <- tooBig< n e p

{-
reduceLemma : (n : Nat)(i j : Nat) ->
  Pr (Eq (Fin (su n)) (Fin (su n))
      (finPlus n (reduce n i) (reduce n j))
      (reduce n (i +N j)))
reduceLemma n i j with divMod i (su n) | divMod j (su n)
reduceLemma n .(mulAdd qi (su n) ri) .(mulAdd qj (su n) rj) | quotRem qi (ri , ip) | quotRem qj (rj , jp) = {!!}
-}
-}
