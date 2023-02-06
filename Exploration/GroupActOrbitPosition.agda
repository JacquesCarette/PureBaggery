module GroupActOrbitPosition where

record _><_ (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open _><_ public

module _ {X : Set} where

  data _~_ (x : X) : X -> Set where
    r~ : x ~ x
  infix 10 _~_

  _~[_>_ : forall x {y z} -> x ~ y -> y ~ z -> x ~ z
  x ~[ r~ > q = q
  _<_]~_ : forall x {y z} -> y ~ x -> y ~ z -> x ~ z
  x < r~ ]~ q = q
  infixr 10 _~[_>_ _<_]~_
  _[QED] : forall x -> x ~ x
  x [QED] = r~
  infixr 11 _[QED]

{-# BUILTIN EQUALITY _~_ #-}

uip : forall {X}{x y : X}{p q : x ~ y} -> p ~ q
uip {X}{x}{.x}{r~}{r~} = r~


_~^ : forall {X}(x : X) -> x ~ x
x ~^ = r~
_~$~_ : forall {S T}
  {f g : S -> T} -> f ~ g ->
  {x y : S} -> x ~ y ->
  f x ~ g y
r~ ~$~ r~ = r~
_$~_ : forall {S T}
  (f : S -> T) ->
  {x y : S} -> x ~ y ->
  f x ~ f y
f $~ q = f ~^ ~$~ q
infixl 12 _~^ _~$~_ _$~_

compEq : {A : Set}{B : A -> Set}
  (q : {a : A}{x y : B a} -> x ~ y)
  {x y : A >< B}
  -> fst x ~ fst y
  -> x ~ y
compEq q {a , b0}{a , b1} r~ = (a ,_) $~ q 

record _<=>_ (S T : Set) : Set where
  field
    _$>_ : S -> T
    _$<_ : T -> S
    _$><_ : (s : S) -> _$<_ (_$>_ s) ~ s
    _$<>_ : (t : T) -> _$>_ (_$<_ t) ~ t
open _<=>_ public

record Group : Set1 where
  field
    Grp : Set
    neu : Grp
    inv : Grp -> Grp
    _&_ : Grp -> Grp -> Grp
  infixr 20 _&_
  field
    neu& : (g : Grp) -> neu & g ~ g
    ass& : (f g h : Grp) -> (f & g) & h ~ f & (g & h)
    inv& : (g : Grp) -> inv g & g ~ neu
  _&inv : (g : Grp) -> g & inv g ~ neu
  g &inv = 
    g & inv g
      < neu& (g & inv g) ]~
    neu & (g & inv g)
      < _& (g & inv g) $~ inv& (inv g) ]~
    (inv (inv g) & inv g) & (g & inv g)
      ~[ ass& _ _ _ >
    inv (inv g) & (inv g & (g & inv g))
      < inv (inv g) &_ $~ ass& _ _ _ ]~
    inv (inv g) & ((inv g & g) & inv g)
      ~[ inv (inv g) &_ $~ (_& inv g $~ inv& g) >
    inv (inv g) & (neu & inv g)
      ~[ inv (inv g) &_ $~ neu& (inv g) >
    inv (inv g) & inv g
      ~[ inv& (inv g) >
    neu
      [QED]
  _&neu : (g : Grp) -> g & neu ~ g
  g &neu =
    g & neu
      < g &_ $~ inv& g ]~
    g & (inv g & g)
      < ass& _ _ _  ]~
    (g & inv g) & g
      ~[ _& g $~ g &inv >
    neu & g
      ~[ neu& g >
    g
      [QED]
  invinv : (g : Grp) -> inv (inv g) ~ g
  invinv g =
    inv (inv g)
      < neu& _ ]~
    neu & inv (inv g)
      < _& inv (inv g) $~ g &inv ]~
    (g & inv g) & inv (inv g)
      ~[ ass& _ _ _ >
    g & (inv g & inv (inv g))
      ~[ g &_ $~ inv g &inv >
    g & neu
      ~[ g &neu >
    g
      [QED]
  invneu : inv neu ~ neu
  invneu =
    inv neu
      < neu& (inv neu) ]~
    neu & inv neu
      ~[ neu &inv >
    neu
      [QED]

{-
record Poset : Set1 where
  field
    Pos : Set
    _c=_ : Pos -> Pos -> Set
    rve : (p : Pos) -> p c= p
    asy : (p q : Pos) -> p c= q -> q c= p -> p ~ q
    xve : (p q r : Pos) -> p c= q -> q c= r -> p c= r
-}

record Action (G : Group)(Orb : Set)(Pos : Orb -> Set) : Set where
  open Group
  field
    act : {o : Orb} -> Grp G -> Pos o -> Pos o
    actNeu : forall {o}(p : Pos o) -> act (neu G) p ~ p
    actAnd : forall g h {o}(p : Pos o) -> act (_&_ G g h) p ~ act h (act g p)
    orbPos : (o : Orb) -> Pos o
    orbAct : {o : Orb}(p : Pos o) -> Grp G >< \ g -> act g (orbPos o) ~ p
  Stab : Orb -> Group
  Grp (Stab o) = Grp G >< \ g -> act g (orbPos o) ~ orbPos o
  neu (Stab o) = neu G , actNeu (orbPos o)
  inv (Stab o) (g , q) = inv G g , (
     act (inv G g) (orbPos o)
       < act (inv G g) $~ q ]~
     act (inv G g) (act g (orbPos o))
       < actAnd g (inv G g) (orbPos o) ]~
     act (_&_ G g (inv G g)) (orbPos o)
       ~[ act $~ _&inv G g ~$~ (orbPos o [QED]) >
     act (neu G) (orbPos o)
       ~[ actNeu (orbPos o) >
     orbPos o
       [QED])
  _&_ (Stab o) (g , p) (h , q) = _&_ G g h , (
    act (_&_ G g h) (orbPos o)
      ~[ actAnd g h (orbPos o) >
    act h (act g (orbPos o))
      ~[ act h $~ p >
    act h (orbPos o)
      ~[ q >
    orbPos o
      [QED])
  neu& (Stab o) (g , q) = compEq uip (neu& G g)
  ass& (Stab o) (f , p) (g , q) (h , r) = compEq uip (ass& G f g h)
  inv& (Stab o) (g , q) = compEq uip (inv& G g)

record Stabat {G : Group}{Orb : Set}{Pos : Orb -> Set}
  (A : Action G Orb Pos)(x : Orb) : Set1 where
  open Group G
  open Action
  field
    SubO : Orb -> Set
    SubP : (o : Orb) -> SubO o -> Set
    subOrbPos : (o : Orb)(s : SubO o) -> SubP o s
    isoP : (o : Orb) -> Pos o <=> (SubO o >< SubP o)
    good : (g : Grp)(q : act A g (orbPos A x) ~ orbPos A x)
           (o : Orb)(s : SubO o)(p : SubP o s) ->
           s ~ fst (isoP o $> (act A g (isoP o $< (s , p))))
    stab : (o : Orb)(s : SubO o)(p : SubP o s) ->
           (Grp >< \ g -> (act A g (orbPos A x) ~ orbPos A x)) >< \ (g , _) ->
           (act A g (isoP o $< (s , subOrbPos o s)))
           ~ (isoP o $< (s , p))

    -- Can we factor good and stab more neatly to make clear that
    -- isoP really partitions each orbit into the equivalence classes
    -- induced by the stabiliser of x?
  SubA : Action (Stab A x) (Orb >< SubO) \ (o , s) -> SubP o s
  act SubA {o , s} (g , q) p
    -- This "with" should probaly be made an explicit helper
    -- to make the subsequent proofs easier to control.
    with isoP o $> (act A g (isoP o $< (s , p)))
       | good g q o s p
  ... | .s , p' | r~ = p'
  actNeu SubA {o , s} p
    with act A neu (isoP o $< (s , p))
       | actNeu A (isoP o $< (s , p))
       | good neu (actNeu A (orbPos A x)) o s p
  ... | z | r~ | g
    with isoP o $> (isoP o $< (s , p))
       | isoP o $<> (s , p)
  actNeu SubA {o , s} p | ._ | r~ | r~ | .s , .p | r~ = r~
  actAnd SubA (g , gq) (h , hq) {o , s} p = {!!}
    -- this is going to be a barrel of laughs...
  {-
    with isoP o $> act A g (isoP o $< (s , p))
       | good g gq o s p
  ... | .s , p' | r~
    with isoP o $> act A h (isoP o $< (s , p'))
       | good h hq o s p'
  ... | .s , p'' | r~ = {!!}
  -}
  orbPos SubA (o , s) = subOrbPos o s
  fst (orbAct SubA {o , s} p) = fst (stab o s p)
  snd (orbAct SubA {o , s} p) with stab o s p
  ... | (g , qx) , qp
    with isoP o $> act A g (isoP o $< (s , subOrbPos o s))
       | (isoP o $>_) $~ qp
       | good g qx o s (subOrbPos o s)
  ... | (s' , p') | b | r~
    with isoP o $> (isoP o $< (s , p)) | isoP o $<> (s , p)
  ... | _ | r~ with r~ <- b = r~
