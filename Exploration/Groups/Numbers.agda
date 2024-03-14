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
infixr 20 _+N_

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
    mul x ((a +N b) -times x) -[ cong{X} (mul x) (hommul (homFromMonoid+N x) a b) >
    mul x (mul (a -times x) (b -times x)) < mulmul- x (a -times x) (b -times x) ]-
    mul (mul x (a -times x)) (b -times x) [QED]

  onlyHomFromMonoid+N : (h : HomMonoid Monoid+N MX)
    -> Pr (Oq (`Nat `> X) (hom h) (_-times (hom h 1)))
  onlyHomFromMonoid+N h = homogTac (`Nat `> X) (hom h) (_-times (hom h 1)) help where
    help : (n : Nat) -> Pr (Oq X (hom h n) (n -times hom h 1))
    help ze = homneu h
    help (su n) = 
      hom h (su n) -[ hommul h 1 n >
      mul (hom h 1) (hom h n) -[ cong{X} (mul (hom h 1)) (help n) >
      mul (hom h 1) (n -times hom h 1) [QED]

mulHom : Nat -> HomMonoid Monoid+N Monoid+N
mulHom x = homFromMonoid+N Monoid+N x

_*N_ : Nat -> Nat -> Nat
n *N x = HomMonoid.hom (mulHom x) n
infixr 30 _*N_

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

  module _ (n : Nat) where
  
    private
      mod-inv-work : (x a c : Nat) -> Nat
      mod-inv-work ze     a c      = c
      mod-inv-work (su x) a ze     = mod-inv-work x (su a) n
      mod-inv-work (su x) a (su c) = mod-inv-work x (su a) c

    {- e.g. if n = 4 and x is 12, initially, we count
      12  0 0
      11  1 4
      10  2 3
       9  3 2
       8  4 1
       7  5 0
       6  6 4
       5  7 3
       4  8 2
       3  9 1
       2 10 0
       1 11 4
       0 12 3

      as *integers*, c - x is always what we're trying to compute

      i.e. su n divides x0 + (c - x)   (where x0 is the initial value)

      the invariants are that a + x = x0 and su n divides a + c
    -}
    
      mod-inv-work-lemma : (x a c : Nat)
        -> El (su n -dividesU (a +N c))
        -> El (su n -dividesU ((a +N x) +N mod-inv-work x a c))
        
      mod-inv-work-lemma ze a c (q , p) = q , naq (
        ((a +N ze) +N c)   -N coNg (_+N c) (paq (mul-neu a)) >
        (a +N c)           -N paq p >
        (q *N su n)        [N])
        
      mod-inv-work-lemma (su x) a ze (q , p)
        with q' , p' <- mod-inv-work-lemma x (su a) n (su q , naq (
          (su (a +N n))       -N coNg su (a +Ncomm n) >
          (su n +N a)         < coNg (su n +N_) (paq (mul-neu a)) N-
          (su n +N (a +N ze)) -N coNg (su n +N_) (paq p) >
          (su n +N q *N su n) -N rn >
          (su q *N su n)  [N]))
        = q' , naq (
          ((a +N su x) +N mod-inv-work x (su a) n)
             -N coNg (_+N mod-inv-work x (su a) n) (a +Nsu x) >
          ((su a +N x) +N mod-inv-work x (su a) n) -N paq p' >
          (q' *N su n) [N])
          
      mod-inv-work-lemma (su x) a (su c) (q , p)
        with q' , p' <- mod-inv-work-lemma x (su a) c (q , naq (
           (su a +N c)    < a +Nsu c N-
           (a +N su c)    -N paq p >
           (q *N su n)    [N]))
           = q' ,  naq (
          ((a +N su x) +N mod-inv-work x (su a) c)
             -N coNg (_+N mod-inv-work x (su a) c) (a +Nsu x) >
          ((su a +N x) +N mod-inv-work x (su a) c) -N paq p' >
          (q' *N su n) [N])

    invN : Nat -> Nat
    invN x = mod-inv-work x ze ze

    invN-lemma : (x : Nat) -> El (su n -dividesU (x +N invN x))
    invN-lemma x = mod-inv-work-lemma x ze ze (ze , <>)
    
  private
    inv4-7 : invN 4 7 =N= 3
    inv4-7 = rn
    inv4-12 : invN 4 12 =N= 3
    inv4-12 = rn
    inv4-5 : invN 4 5 =N= 0
    inv4-5 = rn
    inv4-0 : invN 4 0 =N= 0
    inv4-0 = rn

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

  open Quot `Nat (modEq (su n)) (`Mod-resp (su n))
  
  zeF : G
  zeF = `[ 0 ]

  _+F_ : G -> G -> G
  _+F_ = lifting 2 _+N_
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

  -- move this up when done, but it's not quite right
  {-
  syd-invN : (a0 a1 s : Nat) -> Pr (Oq `Nat (a0 % a1) (s *N su n)) ->
    invN n a0 =N= invN n a1
  syd-invN a0 a1 s q = {!!}
  -}
  private
    lift-=N : (x y : Nat) -> x =N= y -> Pr (Oq (FinSu n) `[ x ] `[ y ])
    lift-=N x y p = homogQuot x y (hide (ze , naq (syd-ze x y p)))
    
    ze+-rep : (x : Nat) -> Pr (Oq (FinSu n) (zeF +F `[ x ]) `[ x ])
    ze+-rep x = lift-=N (ze +N x) x rn

    assoc-rep : (x y z : Nat) -> Pr (Oq (FinSu n) ((`[ x ] +F `[ y ]) +F `[ z ])
                                             (`[ x ] +F (`[ y ] +F `[ z ])))
    assoc-rep x y z = lift-=N ((x +N y) +N z) (x +N (y +N z))
      (paq (Monoid.mulmul- Monoid+N x y z))

  ze+ : (x : G) -> Pr (Oq (FinSu n) (zeF +F x) x)
  ze+ = quotElimPN 1 (\ x -> Oq (FinSu n) (zeF +F x) x) ze+-rep

  assocF : (x y z : G) -> Pr (Oq (FinSu n) ((x +F y) +F z) (x +F (y +F z)))
  assocF = quotElimPN 3 (\ x y z -> Oq (FinSu n) ((x +F y) +F z) (x +F (y +F z)))
    assoc-rep

  inv : G -> G
  inv `[ x ] = `[ invN n x ]

  inv+ : (x : G) -> Pr (Oq (FinSu n) (inv x +F x) zeF)
  inv+ = quotElimPN 1 (\ x -> Oq (FinSu n) (inv x +F x) zeF)
    \ x -> homogQuot (invN n x +N x) ze (hide ((id >><< \ {q} h -> naq (
      ((invN n x +N x) % ze) -N syd-zer _ >
      (invN n x +N x)        -N invN n x +Ncomm x >
      (x +N invN n x)        -N paq h >
      (q *N su n) [N])
    )
     (invN-lemma n x)))

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

--------------

NotBothSu : Nat -> Nat -> P
NotBothSu (su _) (su _) = `Zero
NotBothSu     _      _  = `One

Integer : U
Integer = `Nat `>< \ down -> `Nat `>< \ up -> `Pr (NotBothSu down up)

-- prove these are a group

zeZ : El Integer
zeZ = ze , ze , <>

normZ : Nat -> Nat -> El Integer
normZ (su d) (su u) = normZ d u
normZ  ze        u  = ze   ,  u , <>
normZ (su d)  ze    = su d , ze , <>

_+Z_ : El (Integer `> Integer `> Integer)
(dx , ux , _) +Z (dy , uy , _) = normZ (dx +N dy) (ux +N uy)

invZ : El (Integer `> Integer)
invZ (d , u , p) = u , d , help d u p where
  help : (x y : Nat) -> Pr (NotBothSu x y `=> NotBothSu y x)
  help  ze     ze    p = <>
  help  ze    (su y) p = <>
  help (su x)  ze    p = <>
