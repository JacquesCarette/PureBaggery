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
_~$~_ : forall {S T}{f g : S -> T} -> f ~ g -> {x y : S} -> x ~ y -> f x ~ g y
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

record MonoidOn (X : Set) : Set where
  field
    neut : X
    comb : X -> X -> X
    neutcomb : (x : X) -> comb neut x ~ x
    combneut : (x : X) -> comb x neut ~ x
    combcomb : (x y z : X) -> comb (comb x y) z ~ comb x (comb y z)

  monMiddle : (w x y z : X) ->
    comb (comb w x) (comb y z) ~ comb w (comb (comb x y) z)
  monMiddle w x y z =
    comb (comb w x) (comb y z) ~[ combcomb _ _ _ >
    comb w (comb x (comb y z)) < comb _ $~ combcomb _ _ _ ]~
    comb w (comb (comb x y) z) [QED]

_+N0 : (n : Nat) -> (n +N 0) ~ n
ze +N0 = r~
su n +N0 = su $~ (n +N0)

_+Nsu_ : (n m : Nat) -> (n +N su m) ~ su (n +N m)
ze +Nsu m = r~
su n +Nsu m = su $~ (n +Nsu m)

assoc+N : (x y z : Nat) -> ((x +N y) +N z) ~ (x +N (y +N z))
assoc+N ze y z = r~
assoc+N (su x) y z = su $~ assoc+N x y z

AddNat : MonoidOn Nat
AddNat = record { neut = 0; comb = _+N_;
  neutcomb = \ _ -> r~; combneut = _+N0; combcomb = assoc+N }

comm+N : (x y : Nat) -> (x +N y) ~ (y +N x)
comm+N x ze = x +N0
comm+N x (su y) = 
  (x +N su y) ~[ x +Nsu y >
  su (x +N y) ~[ su $~ comm+N x y >
  su (y +N x) [QED]

module _ {X : Set}(MX : MonoidOn X) where

  open MonoidOn MX

  record GroupFromMonoid : Set where
    field
      nvrt : X -> X
      nvrtcomb : (x : X) -> comb (nvrt x) x ~ neut
    combnvrt : (x : X) -> comb x (nvrt x) ~ neut
    combnvrt x = 
      comb x (nvrt x) < neutcomb _ ]~
      comb neut (comb x (nvrt x)) < comb $~ nvrtcomb _ ~$~ r~ ]~
      comb (comb (nvrt (nvrt x)) (nvrt x)) (comb x (nvrt x))
        ~[ monMiddle _ _ _ _ >
      comb (nvrt (nvrt x)) (comb (comb (nvrt x) x) (nvrt x))
        ~[ comb _ $~ (comb $~ nvrtcomb x ~$~ r~) >
      comb (nvrt (nvrt x)) (comb neut (nvrt x))
        ~[ comb _ $~ neutcomb _ >
      comb (nvrt (nvrt x)) (nvrt x)
        ~[ nvrtcomb _ >
      neut [QED]
    nvrtnvrt : (x : X) -> nvrt (nvrt x) ~ x
    nvrtnvrt x =
      nvrt (nvrt x) < neutcomb _ ]~
      comb neut (nvrt (nvrt x)) < comb $~ combnvrt x ~$~ r~ ]~
      comb (comb x (nvrt x)) (nvrt (nvrt x)) ~[ combcomb _ _ _ >
      comb x (comb (nvrt x) (nvrt (nvrt x)))
        ~[ comb x $~ combnvrt _ >
      comb x neut ~[ combneut _ >
      x [QED]
    nvrtneut : nvrt neut ~ neut
    nvrtneut =
      nvrt neut  < combneut _ ]~
      comb (nvrt neut) neut ~[ nvrtcomb _ >
      neut [QED]
      

module _ where
  open MonoidOn AddNat
  
  mid4+N : (w x y z : Nat) -> ((w +N x) +N (y +N z)) ~ ((w +N y) +N (x +N z))
  mid4+N w x y z =
    ((w +N x) +N (y +N z)) ~[ monMiddle w x y z >
    ((w +N ((x +N y) +N z))) ~[ w +N_ $~ (_+N z $~ comm+N x y) >
    ((w +N ((y +N x) +N z))) < monMiddle w y x z ]~
    ((w +N y) +N (x +N z)) [QED]

module _ {X Y : Set}(MX : MonoidOn X)(MY : MonoidOn Y) where
  open MonoidOn

  record _-Monoid>_ : Set where
    field
      monHom : X -> Y
      monHomNeut : monHom (neut MX) ~ neut MY
      monHomComb : (a b : X) -> monHom (comb MX a b) ~ comb MY (monHom a) (monHom b)

module _ {X : Set}(MX : MonoidOn X) where
  open MonoidOn MX
  open _-Monoid>_
  
  times : X -> AddNat -Monoid> MX
  monHom (times x) ze = neut
  monHom (times x) (su n) = comb x (monHom (times x) n)
  monHomNeut (times x) = r~
  monHomComb (times x) ze b = sym (neutcomb _)
  monHomComb (times x) (su a) b = 
    comb x (monHom (times x) (a +N b)) ~[ comb x $~ monHomComb (times x) a b >
    comb x (comb (monHom (times x) a) (monHom (times x) b)) < combcomb _ _ _ ]~
    comb (comb x (monHom (times x) a)) (monHom (times x) b) [QED]

module _ where
  open _-Monoid>_
  
  _*N_ : Nat -> Nat -> Nat
  x *N y = monHom (times AddNat y) x
  {-
  ze *N y = ze
  su x *N y = y +N (x *N y)
  -}

_<N=_ : Nat -> Nat -> Set
ze <N= _ = One
su n <N= ze = Zero
su n <N= su m = n <N= m

_<N_ : Nat -> Nat -> Set
x <N y = su x <N= y

refl<N= : (n : Nat) -> n <N= n
refl<N= ze = <>
refl<N= (su n) = refl<N= n

trans<N= : (l n m : Nat) -> l <N= n -> n <N= m -> l <N= m
trans<N= ze n m ln nm = <>
trans<N= (su l) (su n) (su m) ln nm = trans<N= l n m ln nm

rw<N : (a b c d : Nat) -> a ~ b -> c ~ d -> a <N c -> b <N d
rw<N a b c d r~ r~ p = p

Fin : Nat -> Set
Fin n = < _<N n >

slackenL : (s d : Nat) -> d <N (su s +N d)
slackenL s ze = <>
slackenL s (su d) = rw<N d d (su s +N d) (s +N su d) r~ (sym (s +Nsu d)) (slackenL s d)

slackenR : (s d : Nat) -> s <N (su s +N d)
slackenR ze d = _
slackenR (su s) d = slackenR s d

tooBig : (n m : Nat) -> (n +N m) <N n -> Zero
tooBig (su n) m l = tooBig n m l

finEqNum : (n : Nat){x y : Fin n} -> fst x ~ fst y -> x ~ y
finEqNum (su n) {ze , <>} {.ze , <>} r~ = r~
finEqNum (su n) {su x , lx} {.(su x) , ly} r~
  = (\ (x , p) -> (su x , p)) $~ finEqNum n {x , lx} {x , ly} r~

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
    (slackenR s d)
 -- rewrite s +N0 = ze , r~ , slackenR s d
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

mod-su-worker-down : (n k d  : Nat) ->
  mod-su-worker n (su n +N k) d (su d +N k) ~ mod-su-worker n k n k
mod-su-worker-down n k ze = r~
mod-su-worker-down n k (su d) = mod-su-worker-down n k d

mod-su-step : (n r : Nat) -> mod-su n (su n +N r) ~ mod-su n r
mod-su-step n r = mod-su-worker-down n r n

mod-su-sod-q : (n q r : Nat) ->
  mod-su n ((q *N su n) +N r) ~ mod-su n r
mod-su-sod-q n ze r = r~
mod-su-sod-q n (su q) r = 
  mod-su n ((su n +N (q *N su n)) +N r) ~[ mod-su n $~ assoc+N (su n) _ _ >
  mod-su n (su n +N ((q *N su n) +N r)) ~[ mod-su-step n ((q *N su n) +N r) >
  mod-su n ((q *N su n) +N r) ~[ mod-su-sod-q n q r >
  mod-su n r [QED]

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

mod-su-idem : (n r : Nat) -> r <N su n -> mod-su n r ~ r
mod-su-idem n r l
  with q , e , l' <- mod-su-good n r (mod-su n r) r~
  = snd (mod-su-already n (r , l) q (mod-su n r) e l')

-----------------------------------------------------------------------

module _ {n : Nat} where

  open _-Monoid>_

  private M = Fin (su n)

  reduce : Nat -> M
  reduce x
    with _ , r , _ , l <- div-mod-su-good n x
       = r , l

  zeF : M
  zeF = reduce 0

  _+F_ : M -> M -> M
  (x , _) +F (y , _) = reduce (x +N y)

  wannaHom : (x y : Nat) -> mod-su n (mod-su n x +N mod-su n y) ~ mod-su n (x +N y)
  wannaHom x y
    with rx <- mod-su n x | qx , ex , lx <- mod-su-good n x _ r~
    with ry <- mod-su n y | qy , ey , ly <- mod-su-good n y _ r~
       = mod-su n (rx +N ry)
           < mod-su-sod-q n (qx +N qy) (rx +N ry) ]~
         mod-su n (((qx +N qy) *N su n) +N (rx +N ry))
           ~[ mod-su n $~ (_+N (rx +N ry) $~ monHomComb (times AddNat (su n)) qx qy) >
         mod-su n (((qx *N su n) +N (qy *N su n)) +N (rx +N ry))
           ~[ mod-su n $~ mid4+N (qx *N su n) (qy *N su n) rx ry >
         mod-su n (((qx *N su n) +N rx) +N ((qy *N su n) +N ry))
           ~[ mod-su n $~ (_+N_ $~ ex ~$~ ey) >
        mod-su n (x +N y) [QED]
  open MonoidOn

  AddModSu : MonoidOn M
  neut AddModSu = zeF
  comb AddModSu = _+F_
  neutcomb AddModSu (y , l) = finEqNum (su n) (mod-su-idem n y l)
  combneut AddModSu (x , l) = finEqNum (su n) (
    mod-su n (x +N 0) ~[ mod-su n $~ (x +N0) >
    mod-su n x ~[ mod-su-idem n x l >
    x [QED])
  combcomb AddModSu (x , lx) (y , ly) (z , lz) = finEqNum (su n) (
    mod-su n (mod-su n (x +N y) +N z)
      < mod-su n $~ (mod-su n (x +N y) +N_ $~ mod-su-idem n z lz) ]~
    mod-su n (mod-su n (x +N y) +N mod-su n z)
      ~[ wannaHom (x +N y) z >
    mod-su n ((x +N y) +N z)
      ~[ mod-su n $~ assoc+N x y z >
    mod-su n (x +N (y +N z))
      < wannaHom x (y +N z) ]~
    mod-su n (mod-su n x +N mod-su n (y +N z))
      ~[ mod-su n $~ ((_+N mod-su n (y +N z)) $~ mod-su-idem n x lx) >
    mod-su n (x +N mod-su n (y +N z)) [QED])

  modHom : AddNat -Monoid> AddModSu
  monHom modHom = reduce
  monHomNeut modHom = r~
  monHomComb modHom a b = finEqNum (su n) (sym (wannaHom a b))

monus : Nat -> Nat -> Nat
monus m ze = m
monus ze (su n) = ze
monus (su m) (su n) = monus m n

monusSlack : (m n : Nat) -> monus m n <N su m
monusSlack m ze = slackenL ze m
monusSlack ze (su n) = <>
monusSlack (su m) (su n) =
  trans<N= (su (monus m n)) (su m) (su (su m))
    (monusSlack m n) (slackenL (su ze) (su m))

monusLemma : (m n : Nat) -> n <N su m -> (n +N monus m n) ~ m
monusLemma m ze l = r~
monusLemma (su m) (su n) l = su $~ monusLemma m n l

module _ {n : Nat} where

  open GroupFromMonoid
  
  ModSu : GroupFromMonoid (AddModSu {n})
  nvrt ModSu (ze , l) = ze , _
  nvrt ModSu (su x , l) = monus n x , monusSlack n x 
  nvrtcomb ModSu (ze , l) = r~
  nvrtcomb ModSu (su x , l) = finEqNum (su n) (
    mod-su n (monus n x +N su x) ~[ mod-su n $~ comm+N _ (su x) >
    mod-su n (su (x +N monus n x))
      ~[ mod-su n $~ (su $~ monusLemma n x (
           trans<N= x (su x) n (slackenL 1 x) l)) >
    mod-su n (su n) < mod-su n $~ (su n +N0) ]~
    mod-su n (su n +N 0)
      ~[ mod-su-step n 0 >
    0 [QED])

{-
  ModSu : GroupFromMonoid (AddModSu {n})
  nvrt ModSu x = inv {su n} x
  nvrtcomb ModSu (x , l) = finEqNum (su n) (
    mod-su n (monus n x +N x) ~[ {!!} >
    mod-su n (x +N monus n x) ~[ mod-su n $~ monusLemma n x l >
    mod-su n n ~[ {!!} >  --
    ze [QED])
-}

{- perhaps...

  define <F as <N on fst
  suppose x : Nat and y : Fin (su n)

  x <N fst y
   <=>
  reduce x <F y
-}

