module Numbers where

-- needs refactored in terms of call graphs?

open import Basics
open import ExtUni
open import Reasoning
open import Group
open import Hom
open import Quotient

record _=N=_ (x y : Nat) : Set where
  constructor paq
  field
    naq : Pr (Oq `Nat x y)
open _=N=_

rn : {n : Nat} -> n =N= n
rn {n} = paq (refl `Nat n)

module _ (x : Nat){y z : Nat} where
  open EQPRF `Nat
  _-N_>_ : x =N= y -> y =N= z -> x =N= z
  _-N_>_ (paq p) (paq q) = paq (trans x y z p q)
  _<_N-_ : y =N= x -> y =N= z -> x =N= z
  _<_N-_ (paq p) (paq q) = paq (trans x y z (!_ {y}{x} p) q)

  infixr 2 _-N_>_ _<_N-_
  
_[N] : (n : Nat) -> n =N= n
n [N] = rn
infixr 3 _[N]

coNg : (f : Nat -> Nat){x y : Nat} -> x =N= y -> f x =N= f y
coNg f {x}{y} (paq q) = paq (refl (`Nat `> `Nat) f x y q)

-- su injective
sui : {x y : Nat} -> su x =N= su y -> x =N= y
sui (paq q) = paq q

_+N_ : Nat -> Nat -> Nat
ze +N y = y
su x +N y = su (x +N y)

_+Ninj : (n x y : Nat) -> (n +N x) =N= (n +N y) -> x =N= y
(ze +Ninj) x y q = q
(su n +Ninj) x y q = (n +Ninj) x y (sui q)

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
  open Monoid MX
  open EQPRF X

  _-times_ :  El (`Nat `> X `> X)
  ze   -times x = neu
  su n -times x = mul x (n -times x)

  open HomMonoid
  homFromMonoid+N : El X -> HomMonoid Monoid+N MX
  hom (homFromMonoid+N x) n = n -times x
  homneu (homFromMonoid+N x) = refl X neu
  hommul (homFromMonoid+N x) ze b = 
    (b -times x) < mulneu- (b -times x) ]-
    mul neu (b -times x) [QED]
  hommul (homFromMonoid+N x) (su a) b = 
    mul x ((a +N b) -times x) -[ cong (mul x) (hommul (homFromMonoid+N x) a b) >
    mul x (mul (a -times x) (b -times x)) < mulmul- x (a -times x) (b -times x) ]-
    mul (mul x (a -times x)) (b -times x) [QED]

  onlyHomFromMonoid+N : (h : HomMonoid Monoid+N MX)
    -> Pr (Oq (`Nat `> X) (hom h) (_-times (hom h 1)))
  onlyHomFromMonoid+N h = homogTac (`Nat `> X) (hom h) (_-times (hom h 1)) help where
    help : (n : Nat) -> Pr (Oq X (hom h n) (n -times hom h 1))
    help ze = homneu h
    help (su n) = 
      hom h (su n) -[ hommul h 1 n >
      mul (hom h 1) (hom h n) -[ cong (mul (hom h 1)) (help n) >
      mul (hom h 1) (n -times hom h 1) [QED]

mulHom : Nat -> HomMonoid Monoid+N Monoid+N
mulHom x = homFromMonoid+N Monoid+N x

_*N_ : Nat -> Nat -> Nat
n *N x = HomMonoid.hom (mulHom x) n

_-dividesU_ : Nat -> Nat -> U
n -dividesU m = `Nat `>< \ q -> `Pr (Oq `Nat m (q *N n))
_-divides_ : Nat -> Nat -> P
n -divides m = `In (n -dividesU m)

-- % is symmetric difference
_%_ : Nat -> Nat -> Nat
ze   %    y = y
su x % ze   = su x
su x % su y = x % y

trichotomy : (x y : Nat)(M : Nat -> Nat -> Nat -> U)
  -> ((a d : Nat) -> El (M a (a +N su d) (su d)))
  -> ((n : Nat) -> El (M n n ze))
  -> ((a d : Nat) -> El (M (a +N su d) a (su d)))
  -> El (M x y (x % y))
trichotomy ze ze M l e g = e ze
trichotomy ze (su y) M l e g = l ze y
trichotomy (su x) ze M l e g = g ze x
trichotomy (su x) (su y) M l e g = trichotomy x y (\ x y z -> M (su x) (su y) z)
  (su - l)
  (su - e)
  (su - g)

syd-sym : (x y : Nat) -> (x % y) =N= (y % x)
syd-sym  ze     ze    = rn
syd-sym  ze    (su y) = rn
syd-sym (su x)  ze    = rn
syd-sym (su x) (su y) = syd-sym x y

syd-ze : (x y : Nat) -> x =N= y -> (x % y) =N= ze
syd-ze ze     ze     q = rn 
syd-ze (su x) (su y) q = syd-ze x y (sui q)

syd+N : (x y z : Nat) -> z =N= (x +N y) -> (x % z) =N= y
syd+N ze     y     z  p = p
syd+N (su x) y (su z) p = syd+N x y z (sui p)

syd-can : (x y z : Nat) -> ((x +N y) % (x +N z)) =N= (y % z)
syd-can ze y z = rn
syd-can (su x) y z = syd-can x y z

-- this is not free as _%_ analyzes its lhs first
syd-zer : (x : Nat) -> (x % ze) =N= x
syd-zer ze = rn
syd-zer (su x) = rn

module _ where

  open Monoid Monoid+N

  _+Nsu_ : (x y : Nat) -> (x +N su y) =N= (su (x +N y))
  ze   +Nsu y = rn
  su x +Nsu y = coNg su (x +Nsu y)

  _+Ncomm_ : (x y : Nat) -> (x +N y) =N= (y +N x)
  x +Ncomm ze = paq (mul-neu x)
  x +Ncomm su y =
    (x +N su y) -N x +Nsu y >
    (su x +N y) -N coNg su (x +Ncomm y) >
    (su y +N x) [N] -- trans (x +N su y) (su (x +N y)) (su (y +N x)) (x +Nsu y) (x +Ncomm y)

  _*Nze : (x : Nat) -> (x *N ze) =N= ze
  ze *Nze = rn
  su x *Nze = x *Nze
 
module _ where

  open Monoid Monoid+N

  syd-chop : (a b c d : Nat) -> Pr (Oq `Nat (a +N b) (c +N d) `=> Oq `Nat (a % c) (b % d))
  syd-chop a b c d = trichotomy a c (\ a c z -> `Pr (Oq `Nat (a +N b) (c +N d) `=> Oq `Nat z (b % d)))
    (\ x y q -> naq (
      su y                < syd+N d (su y) (su y +N d) (su y +Ncomm d) N-
      (d % (su y +N d))   -N syd-sym d (su y +N d) >
      ((su y +N d) % d)   < coNg (_% d) ((x +Ninj) b (su y +N d) (
        (x +N b)             -N paq q >
        ((x +N su y) +N d)   -N paq (mulmul- x (su y) d) >
        (x +N su (y +N d))   [N])) N-
      (b % d)             [N]))
    (\ n q -> naq (
      ze       < syd-ze b d ((n +Ninj) b d (paq q)) N-
      (b % d)  [N]))
    \ x y q -> naq (
      (su y)               < syd+N b (su y) (su y +N b) (su y +Ncomm b) N-
      (b % (su y +N b))    -N coNg (b %_) ((x +Ninj) (su y +N b) d (
        (x +N su (y +N b))   -N paq (mul-mul x (su y) b) >
        ((x +N su y) +N b)   -N paq q >
        (x +N d)             [N])) >
      (b % d)              [N])

  syd-mid : (x y z : Nat)(M : Nat -> U) -> El (
       M ((x % y) +N (y % z))
    `> M ((x % y) % (y % z))
    `> M (x % z))
  syd-mid x y z M = trichotomy x y (\ x y xy -> M (xy +N (y % z)) `>  M (xy % (y % z)) `> M (x % z))
    -- up, then what?
    (\ x xy -> trichotomy (x +N su xy) z (\ a z d -> `Pr (Oq `Nat a (x +N su xy)) `> M (su (xy +N d)) `> M (su xy % d) `> M (x % z))
      -- up more
      (\ w d q m _ -> subst `Nat (naq (
        (su xy +N su d)               < syd+N x (su xy +N su d) _ (paq (mulmul- x (su xy) (su d))) N-
        (x % ((x +N su xy) +N su d))  < coNg ((_+N su d) - (x %_)) (paq q) N-
        (x % (w +N su d))             [N]))
        M m)
      -- along
      (\ w q _ -> subst `Nat (naq (
        su xy    < syd+N x (su xy) w (paq q) N-
        (x % w)  [N]))
        M)
      -- back down
      (\ w d q _ -> subst `Nat (naq (
        (xy % d)  < paq (syd-chop x xy w d (naq (
          (su x +N xy)  < x +Nsu xy N-
          (x +N su xy)  < paq q N-
          (w +N su d)   -N w +Nsu d >
          (su w +N d)   [N]))) N-
        (x % w)   [N]))
        M)
      (naq ((x +N su xy) [N])))
    -- along
    (\ _ _ m -> m)
    -- down, then what?
    \ y yx -> trichotomy y z (\ y z d -> M (su (yx +N d)) `> M (su yx % d) `> M ((y +N su yx) % z))
      -- back up
      (\ w d _ -> subst `Nat (naq (
        (yx % d)                      < syd-can w (su yx) (su d) N-
        ((w +N su yx) % (w +N su d))  [N]))
        M)
      -- along
      (\ w _ -> subst `Nat (naq (
        su yx < syd+N w (su yx) (w +N su yx) rn N-
        (w % (w +N su yx)) -N syd-sym w (w +N su yx) >
        ((w +N su yx) % w) [N]))
        M)
      -- down more
      \ w d m _ -> subst `Nat (naq (
        (su yx +N su d) < syd+N w (su yx +N su d) ((w +N su d) +N su yx) ((
           ((w +N su d) +N su yx) -N paq (mulmul- w (su d) (su yx)) >
           (w +N (su d +N su yx)) -N coNg (w +N_) (su d +Ncomm su yx) >
           (w +N su (yx +N su d)) [N])
        ) N-
        (w % ((w +N su d) +N su yx)) -N syd-sym w _ >
        (((w +N su d) +N su yx) % w) [N]))
        M m

-- HERE

  syd-mul : (a b n : Nat) -> ((a *N n) % (b *N n)) =N= ((a % b) *N n)
  syd-mul ze b n = rn
  syd-mul (su a) ze n = syd-zer (su a *N n)
  syd-mul (su a) (su b) n = 
    (n +N (a *N n)) % (n +N (b *N n)) -N syd-can n _ _ >
    (a *N n) % (b *N n)               -N syd-mul a b n >
    ((a % b) *N n)                    [N]

  private
    -- compute-shifted-scale
    -- will only be called from this file
    compute-shifted-scale : (a n x cnt : Nat) -> Nat
    -- x and n reach 0 at the same time
    compute-shifted-scale a n ze ze = a
    -- x has reached 0 in this interval
    compute-shifted-scale a n ze (su cnt) = a
    -- x still has to go, but we've exhausted our n supply, next round
    compute-shifted-scale a n (su x) ze = su (compute-shifted-scale a n x n)
    -- keep going
    compute-shifted-scale a n (su x) (su cnt) = compute-shifted-scale a n x cnt
  
  -- in strides of n, where is x ?
  -- i.e. q such that q*n <= x < (q+1)*n
  scale : (n x : Nat) -> Nat
  scale n x = compute-shifted-scale 0 n x n

  -- a few tests, to make sure we get the right answer
  private
    s13 : scale 10 13 =N= 1
    s13 = rn
    s13g : let q = 10 *N scale 10 13 in (q +N (13 % q)) =N= 13
    s13g = rn

  invN : Nat -> Nat -> Nat
  invN n x = let q = (su n) *N scale (su n) x in x % q

--------------------------------

module _ (n : Nat) where

  open EQPRF `Nat
  open Monoid Monoid+N
  open HomMonoid (mulHom n)

  private
    addLem : (a b : Nat) -> El
      (n -dividesU a `> n -dividesU b `> n -dividesU (a +N b))
    addLem a b (qa , pa) (qb , pb) = qa +N qb ,
      naq (
        a +N b                 -N coNg (_+N b) (paq pa) >
        (qa *N n) +N b         -N coNg ((qa *N n) +N_) (paq pb) >
        (qa *N n) +N (qb *N n) < paq (hommul qa qb) N-
        (qa +N qb) *N n        [N])

    %Lem : (a b : Nat) -> El
      (n -dividesU a `> n -dividesU b `> n -dividesU (a % b))
    %Lem a b (qa , pa) (qb , pb) = qa % qb , naq (
      a % b                 -N coNg (a %_) (paq pb) >
      a % (qb *N n)         -N coNg (_% (qb *N n)) {a} (paq pa) >
      (qa *N n) % (qb *N n) -N syd-mul qa qb n >
      (qa % qb) *N n        [N])

  modEq : Nat -> Nat -> P
  modEq x y = n -divides (x % y)
  
  `Mod-resp : Equiv Nat (\ i j -> Pr (modEq i j))
  `Mod-resp =
    (record
      { eqR = \ x -> hide (ze , naq (syd-ze x x rn))
      ; eqS = \ x y (hide h) -> hide (fst h , (
         y % x -[ naq (syd-sym y x) >
         x % y -[ snd h >
         (fst h *N n) [QED]))
      ; eqT = \ x y z (hide xy) (hide yz) ->
          syd-mid x y z (\ w -> `Pr (`In (`Nat `>< (\ s -> `Pr (Oq `Nat w (s *N n))))))
            (hide (addLem (x % y) (y % z) xy yz))
            (hide (%Lem (x % y) (y % z) xy yz))
      })
  
  `Mod : U
  `Mod = `Quotient `Nat modEq `Mod-resp

FinSu : Nat -> U
FinSu = su - `Mod

-- Build up the pieces that make `Fin` into a group
module BuildFin (n : Nat) where
  private
    G : Set
    G = El (FinSu n)

  zeF : G
  zeF = `[ 0 ]

  _+F_ : G -> G -> G
  _+F_ = lifting `Nat (modEq (su n)) (`Mod-resp (su n)) 2 _+N_
      ( (\ a0 a1 ar b -> mapHide (id >><< \ {s} q -> naq (
                ((a0 +N b) % (a1 +N b)) -N coNg (_% (a1 +N b)) (a0 +Ncomm b) >
                ((b +N a0) % (a1 +N b)) -N coNg ((b +N a0) %_) (a1 +Ncomm b) >
                ((b +N a0) % (b +N a1)) -N syd-can b a0 a1 >
                (a0 % a1) -N paq q >
                (s *N su n) [N]))
           ar)
      , \ a -> (\ b0 b1 -> mapHide (id >><< (\ {s} q -> naq (
                  ((a +N b0) % (a +N b1)) -N syd-can a b0 b1 >
                  (b0 % b1) -N paq q >
                  (s *N su n) [N]))))
            , _)


  ze+ : (x : G) -> Pr (Oq (FinSu n) (zeF +F x) x)
  ze+ `[ x ] = hide (x , x ,
    hide (ze , naq (syd-ze x x rn)) ,
    refl `Nat x ,
    hide (ze , naq (syd-ze x x rn)))

{-
  assocF : (x y z : G) -> Pr (Oq (Fin n) ((x +F y) +F z) (x +F (y +F z)))
  assocF `[ x ] `[ y ] `[ z ] = hide (
    ((x +N y) +N z) ,
    (x +N (y +N z)) ,
    hide (ze , naq (syd-ze ((x +N y) +N z) _ rn)) ,
    Monoid.mulmul- Monoid+N x y z  ,
    hide (ze , naq (syd-ze (x +N (y +N z)) _ rn)))

  inv : G -> G
  inv `[ x ] = `[ invN n x ]

  -- more this proof up when it's done
  inv-add : (n x : Nat) ->
    let q = scale (su n) x in (invN n x +N x) =N= (q *N su n)
  inv-add n ze = 
    (n *N 0) +N 0 -N paq (Monoid.mul-neu Monoid+N (n *N 0)) >
    n *N 0        -N n *Nze >
    0             [N]
  inv-add n (su x) = 
    (invN n (su x) +N su x)            -N rn >
    ((su x % (su n *N q)) +N su x)     -N {!inv-add n x!} >
    q *N su n                [N] 
    where
      q = scale (su n) (su x)
      q' = scale (su n) x
      -- inv-add n x == invN n x +N x = q' *N su n
      -- (x % (su n *N q')) +N x == q' *N su n
      
  inv+ : (x : G) -> Pr (Oq (Fin n) (inv x +F x) zeF)
  inv+ `[ x ] = hide (
    invN n x +N x ,
    (q *N su n) ,
    hide (ze , naq (syd-ze (invN n x +N x) _ rn)) ,
    naq (inv-add n x) ,
    hide (q ,
      naq (syd-zer (q *N su n))))
    where
      q : Nat
      q = scale (su n) x
      
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

-}
