module Basics where

--------------------------------------------------------------------
-- First, a lot of kit to get started

-- Using proof irrelevance keeps us from using details that we
-- should not care about. [Also brings in complications.]
record Hide (X : Set) : Set where
  constructor hide
  field
    .expose : X
open Hide public

mapHide : forall {S T} -> (S -> T) -> Hide S -> Hide T
mapHide f (hide s) = hide (f s)


--------------
-- empty, singleton and (exactly) 2 point set along with eliminator
data Zero' : Set where
Zero = Hide Zero'
naughtE : forall {k}{X : Set k } -> Zero -> X
naughtE (hide ())

record One : Set where constructor <>

data Two : Set where `0 `1 : Two
_<01>_ : forall {k}{P : Two -> Set k} -> P `0 -> P `1 -> (b : Two) -> P b
(p0 <01> p1) `0 = p0
(p0 <01> p1) `1 = p1
not : Two -> Two
not = `1 <01> `0

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
  [:_:] <:_:> : (I -> Set) -> Set
  [: P :] = forall {i} -> P i
  <: P :> = _ >< P

-- uncurry
/\_ : {S : Set}{T : S -> Set}{P : S >< T -> Set}
   -> ((s : S)(t : T s) -> P (s , t))
   -> (st : S >< T) -> P st
(/\ k) (s , t) = k s t

id : forall {k}{X : Set k} -> X -> X
id x = x

kon_ : forall {k l}{X : Set k}{Y : Set l} -> X -> Y -> X
kon_ x _ = x
infixr 20 kon_

-- dependent function composition, pipe style
_-_ : forall {i j k}{A : Set i}{B : A -> Set j}{C : (a : A) -> B a -> Set k}
  (f : (a : A) -> B a)
  (g : {a : A}(b : B a) -> C a b)
  (a : A)
  -> C a (f a)
(f - g) a = g (f a)
infixl 15 _-_

flip : forall {i j k}{A : Set i}{B : Set j}{C : A -> B -> Set k}
  (f : (a : A)(b : B) -> C a b)
  (b : B)(a : A) -> C a b
flip f b a = f a b

-- Parallel application of a pair of functions onto a pair.
_>><<_ : forall {S S' : Set}{T : S -> Set}{T' : S' -> Set}
  (f : S -> S')(g : {s : S} -> T s -> T' (f s))
  -> (S >< T) -> (S' >< T')
(f >><< g) (s , t) = f s , g t

-- Nat is useful for non-trivial examples
data Nat : Set where ze : Nat ; su : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

-- Lists come in handy too
data List (A : Set) : Set where
  [] : List A
  _,-_ : A -> List A -> List A
infixr 20 _,-_

list : {A B : Set} -> (A -> B) -> List A -> List B
list f [] = []
list f (x ,- xs) = f x ,- list f xs

cataList : forall {b} {A : Set} {B : Set b} -> (A -> B -> B) -> B -> List A -> B
cataList _ b [] = b
cataList _/_ b (x ,- xs) = x / cataList _/_ b xs

{-
data _-in_ {A : Set} (a : A) : (L : List A) -> Set where
  ze : {as : List A} -> a -in (a ,- as)
  su : {b : A} {as : List A} -> a -in as -> a -in (b ,- as)
-}

module _ {A : Set} where

  -- we plan to use lists of arities (themselves lists) as signatures
  -- with list membership as operation selection

  -- thinnings (sublist selection) then talk about theory inclusion

  data _<=_ : List A -> List A -> Set where
    -- a ^- th means "a is excluded, with th for the rest"
    -- ^ is "caret", i.e. "it is missing"
    _^-_ : forall {xs ys} a -> xs <= ys ->       xs  <= (a ,- ys)
    -- a ,- th means "a is included"
    _,-_ : forall {xs ys} a -> xs <= ys -> (a ,- xs) <= (a ,- ys)
    [] : [] <= []

  _-in_ : A -> List A -> Set
  a -in xs = (a ,- []) <= xs

  io : forall {xs} -> xs <= xs
  io {[]} = []
  io {x ,- xs} = x ,- io {xs}

  no : forall {xs} -> [] <= xs
  no {[]} = []
  no {x ,- xs} = x ^- no

  data [_-<_]=_ : forall {xs ys zs}
    -> (th : xs <= ys)(ph : ys <= zs)(ps : xs <= zs) -> Set where

    _^-_ : forall a {xs ys zs}
      -> {th : xs <= ys}{ph : ys <= zs}{ps : xs <= zs}
      -> [ th -< ph ]= ps
      -> [ th -< (a ^- ph) ]= (a ^- ps)

    _^,-_ : forall a {xs ys zs}
      -> {th : xs <= ys}{ph : ys <= zs}{ps : xs <= zs}
      -> [ th -< ph ]= ps
      -> [ (a ^- th) -< (a ,- ph) ]= (a ^- ps)

    _,-_ : forall a {xs ys zs}
      -> {th : xs <= ys}{ph : ys <= zs}{ps : xs <= zs}
      -> [ th -< ph ]= ps
      -> [ (a ,- th) -< (a ,- ph) ]= (a ,- ps)

    [] : [ [] -< [] ]= []

  tri : forall {xs ys zs}(th : xs <= ys)(ph : ys <= zs) -> <: [ th -< ph ]=_ :>
  tri th (a ^- ph) = let _ , v = tri th ph in _ , (a ^- v)
  tri (.a ^- th) (a ,- ph) = let _ , v = tri th ph in _ , (a ^,- v)
  tri (.a ,- th) (a ,- ph) = let _ , v = tri th ph in _ , (a ,- v)
  tri [] [] = _ , []
  
  _-<_ : forall {xs ys zs}(th : xs <= ys)(ph : ys <= zs) -> xs <= zs
  th -< ph = fst (tri th ph)

  -- th /#\ ph means that th and ph *partition* their shared target
  data _/#\_ : forall {xs us ys}(th : xs <= us) (ph : ys <= us) -> Set where
    _,^-_ : forall a {xs us ys}{th : xs <= us}{ph : ys <= us}
         -> th /#\ ph
         -> (a ,- th) /#\ (a ^- ph)
    _^,-_ : forall a {xs us ys}{th : xs <= us}{ph : ys <= us}
         -> th /#\ ph
         -> (a ^- th) /#\ (a ,- ph)
    [] : [] /#\ []

  _-not : forall {xs us}(th : xs <= us) -- if th selects a subset of us
       -> <: _<= us :> >< \ (_ , ph)    -- there's another subset, ph
       -> th /#\ ph                     -- such that th and ph partition us
  (a ^- th) -not = let _ , w = th -not in _ , (a ^,- w)
  (a ,- th) -not = let _ , w = th -not in _ , (a ,^- w)
  [] -not = _ , []

  _-sub_ : List A -> List A -> Set
  xs -sub ys = forall {a} -> a -in xs -> a -in ys

  atomize : forall {xs ys} -> xs <= ys -> xs -sub ys
  atomize th i = i -< th

  {- this is doomed
  ezimota : forall {xs ys} -> xs -sub ys -> xs <= ys
  ezimota {[]} {ys} sb = no
  ezimota {x ,- xs} {ys} sb with sb (x ,- no)
  ... | a ^- i = a ^- ezimota {!!}
  ... | .x ,- i = x ,- ezimota {!!}
  -- there is no reason why a -sub proof should preserve the order
  -- of duplicated elements
  -}

