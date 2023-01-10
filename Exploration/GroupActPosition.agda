module GroupActPosition where

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

record Poset : Set1 where
  field
    Pos : Set
    _c=_ : Pos -> Pos -> Set
    rve : (p : Pos) -> p c= p
    asy : (p q : Pos) -> p c= q -> q c= p -> p ~ q
    xve : (p q r : Pos) -> p c= q -> q c= r -> p c= r

record Action (P : Poset)(G : Group) : Set where
  open Poset P
  open Group G
  field
    _%_ : Pos -> Grp -> Pos
  infixl 20 _%_
  field
    _%neu : (p : Pos) -> p % neu ~ p
    act&  : (p : Pos)(g h : Grp) -> p % (g & h) ~ p % g % h
    actc= : (p q : Pos)(g : Grp) -> p c= q -> (p % g) c= (q % g)
  actinj : (p q : Pos)(g : Grp) ->
    p % g ~ q % g -> p ~ q
  actinj p q g h =
    p
      < p %neu ]~
    p % neu
      < p %_ $~ g &inv ]~
    p % (g & inv g)
      ~[ act& p g (inv g) >
    p % g % inv g
      ~[ _% inv g $~ h >
    q % g % inv g
      < act& q g (inv g) ]~
    q % (g & inv g) 
      ~[ q %_ $~ g &inv >
    q % neu
      ~[ q %neu >
    q
      [QED]

module _ (X : Set) where
  open Poset
  
  Discrete : Poset
  Pos Discrete = X
  _c=_ Discrete = _~_
  rve Discrete p = r~
  asy Discrete p .p r~ r~ = r~
  xve Discrete p .p .p r~ r~ = r~
  
module _ (G : Group) where
  open Group G
  P = Discrete Grp
  open Poset P
  open Action
  Self : Action P G
  _%_ Self p g = p & g
  _%neu Self p = p &neu
  act& Self p g h = p & (g & h) < ass& _ _ _ ]~ (p & g) & h [QED]
  actc= Self p .p q r~ = r~

record One : Set where constructor <>

module _ where
  open Group
  Trivial : Group
  Grp Trivial = One
  neu Trivial = _
  inv Trivial = _
  _&_ Trivial = _
  neu& Trivial g = r~
  ass& Trivial f g h = r~
  inv& Trivial g = r~

module _ (P : Poset) where
  open Poset P
  open Action
  open Group Trivial
  Rigid : Action P Trivial
  _%_ Rigid p <> = p
  _%neu Rigid p = r~
  act& Rigid p g h = r~
  actc= Rigid p q g h = h

record _><_ (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open _><_

data Zero : Set where

_#_ : {X : Set} -> X -> X -> Set
x # y = x ~ y -> Zero

postulate
  irref : forall {X : Set}{p q : X -> Zero} -> p ~ q

_-without_ : (X : Set)(x : X) -> Set
X -without x = X >< \ y -> y # x

eqWithout : {X : Set}(x : X){a b : X -without x}
  -> fst a ~ fst b -> a ~ b
eqWithout x {a , _} {.a , _} r~ = a ,_ $~ irref

module _ (P : Poset) where
  open Poset
  _-_ : Pos P -> Poset
  Pos (_-_ p) = Pos P -without p
  _c=_ (_-_ p) (q , _) (r , _) = _c=_ P q r
  rve (_-_ p) (q , _) = rve P q
  asy (_-_ p) (q , _) (r , _) h k with r~ <- asy P q r h k = q ,_ $~ irref
  xve (_-_ p) (q , _) (r , _) (s , _) h k = xve P q r s h k

module _ {P : Poset}{G : Group}(A : Action P G) where
  open Poset P
  open Group
  open Action A
  Stabilizer : Pos -> Set
  Stabilizer p = Grp G >< \ g -> p % g ~ p
  eqStab : {p : Pos}{x y : Stabilizer p} -> fst x ~ fst y -> x ~ y
  eqStab {p} {g , gq} {.g , hq} r~ = g ,_ $~ uip
  Stab : Pos -> Group
  Grp (Stab p) = Stabilizer p
  neu (Stab p) = neu G , (_%neu p)
  inv (Stab p) (g , q) = inv G g , (
    p % inv G g
      ~[ actinj _ _ g (
        p % inv G g % g
          < act& p (inv G g) g ]~
        p % (_&_ G (inv G g) g)
          ~[ p %_ $~ inv& G g >
        p % neu G
          ~[ _%neu p >
        p
          < q ]~
        p % g
          [QED])
      >
    p
      [QED])
  _&_ (Stab p) (g , gq) (h , hq) = _&_ G g h , (
    p % (_&_ G g h)
      ~[ act& p g h >
    p % g % h
      ~[ _% h $~ gq >
    p % h
      ~[ hq >
    p
      [QED])
  neu& (Stab p) (g , gq) = eqStab (neu& G g)
  ass& (Stab p) (f , fq) (g , gq) (h , hq) = eqStab (ass& G f g h)
  inv& (Stab p) (g , gq) = eqStab (inv& G g)

module _ {P : Poset}{G : Group}(A : Action P G) where
  open Poset
  open Group
  open Action
  module _ (p : Pos P) where
    _!_ : Action (P - p) (Stab A p)
    _%_ _!_ (q , a) (g , gq) = _%_ A q g , \ h ->
      a (actinj A q p g (_%_ A q g ~[ h > p < gq ]~ _%_ A p g [QED]))
    _%neu _!_ (q , a) = eqWithout p (_%neu A q)
    act& _!_ (q , a) (g , gq) (h , hq)  = eqWithout p (act& A q g h)
    actc= _!_ (q , a) (r , b) (g , gq) l = actc= A q r g l


