module Thinnings where

open import Basics

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

  infixr 20 _^-_ _^,-_

  _-in_ : A -> List A -> Set
  a -in xs = (a ,- []) <= xs

  -- identity thinning
  io : forall {xs} -> xs <= xs
  io {[]} = []
  io {x ,- xs} = x ,- io {xs}

  -- empty thinning
  no : forall {xs} -> [] <= xs
  no {[]} = []
  no {x ,- xs} = x ^- no

  -- singleton thinning as a number (tryptich)
  -- minimal evidence of being in-range
  InRange : Nat -> List A -> Set
  InRange _      []       = Zero
  InRange ze     (x ,- l) = One
  InRange (su n) (x ,- l) = InRange n l

  -- given that evidence, retrieve
  findInRange : (i : Nat) -> (l : List A) -> InRange i l -> A
  findInRange ze     (x ,- l) ir = x
  findInRange (su i) (x ,- l) ir = findInRange i l ir

  -- and now singleton thinning at that (good) location
  sing : (i : Nat) -> {l : List A} {ir : InRange i l} -> findInRange i l ir -in l
  sing ze     {x ,- l} {ir} = x ,- no
  sing (su i) {x ,- l} {ir} = x ^- sing i {l} {ir}
  
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

  module _ (R : A -> Set) where

    All : List A -> Set
    All []        = One
    All (t ,- ts) = R t * All ts

  module _ {R : A -> Set} (S : (a : A) -> R a -> Set) where

    Alll : (as : List A) -> (rs : All R as) -> Set
    Alll [] _ = One
    Alll (a ,- as) (r , rs) = S a r * Alll as rs

  module _ {R : A -> Set} where
  
    select : forall {ss ts} -> ss <= ts -> All R ts -> All R ss
    select (a ^- th) (r , rs) = select th rs
    select (a ,- th) (r , rs) = r , select th rs
    select [] rs = <>

    only : forall {s} -> All R (s ,- []) -> R s
    only = fst

    project : {ss : List A} -> All R ss -> [! (_-in ss) -:> R !]
    project rs i = only (select i rs)

    tabulate : {ss : List A} -> [! (_-in ss) -:> R !] -> All R ss
    tabulate {[]}      f = <>
    tabulate {x ,- ss} f = f (x ,- no) , tabulate {ss} ((x ^-_) - f)

    zAll : (ss : List A) -> All R ss -> List (A >< R)
    zAll [] <> = []
    zAll (s ,- ss) (r , rs) = (s , r) ,- zAll ss rs

    pureAll : [! R !] -> [! All R !]
    pureAll r {[]} = <>
    pureAll r {s ,- ss} = r , pureAll r

    -- pronounced 'riffle'
    _/<_>\_ : forall {ss us ts}{th : ss <= us}{ph : ts <= us}
      -> All R ss
      -> th /#\ ph
      -> All R ts
      -> All R us
    xs /< a ^,- p >\ (y , ys) = y , (xs /< p >\ ys)
    (x , xs) /< a ,^- p >\ ys = x , (xs /< p >\ ys)
    xs /< [] >\ ys           = <>

  module _ {R : A -> Set} {S : (a : A) -> R a -> Set} where

    -- pronounced 'rifffle'
    _/<<_>>\_ : forall {ss us ts}{th : ss <= us}{ph : ts <= us}
      {Rss : All R ss} -> Alll S ss Rss -> (part : th /#\ ph)
      -> {Rts : All R ts} -> Alll S ts Rts
      -> Alll S us (Rss /< part >\ Rts)
    asss        /<< a ^,- part >>\ (as , asts) = as , (asss /<< part >>\ asts)
    (as , asss) /<< a ,^- part >>\ asts        = as , (asss /<< part >>\ asts)
    _           /<< []         >>\ _           = <>
    

  coords : {ss : List A} -> All (_-in ss) ss
  coords = tabulate id
    
  infixl 11 _<*All*>_
  _<*All*>_ :  {S T : A -> Set}
              -> [! All (S -:> T) -:> All S -:> All T !]
  _<*All*>_ {_} {_} {[]} <> <> = <>
  _<*All*>_ {_} {_} {a ,- as} (f , fs) (s , ss) = f s , fs <*All*> ss

  mapAll : {S T : A -> Set}
              -> [! S -:> T !]
              -> [! All S -:> All T !]
  mapAll f ss = pureAll f <*All*> ss

zAllSelect : {A : Set}{R : A -> Set}{ss ts : List A}(th : ss <= ts)(rs : All R ts)
  -> zAll ss (select th rs) <= zAll ts rs
zAllSelect (a ^- th) (r , rs) = (a , r) ^- zAllSelect th rs
zAllSelect (a ,- th) (r , rs) = (a , r) ,- zAllSelect th rs
zAllSelect [] rs = []

