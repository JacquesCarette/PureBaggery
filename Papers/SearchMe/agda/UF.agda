module UF where

open import Basics
open import UE

data UF : Set
[_]F : UF -> Set

data UF where
  `[_] : UE -> UF
  _`><_ : (S : UF)(T : [ S ]F -> UF) -> UF

-- skipping _`->_

[ `[ N ] ]F = [ N ]E
[ S `>< T ]F = [ S ]F >< \ s -> [ T s ]F

_~F>_ : (S : UF)(T : [ S ]F -> Set) -> Set
data _-F>_ (S : UF)(T : [ S ]F -> Set) : Set where
  <_> : S ~F> T -> S -F> T
`[ N ] ~F> T = N  -E> T
(R `>< S) ~F> T = R -F> \ r -> S r -F> \ s -> T (r , s)

\\F : {S : UF}{T : [ S ]F -> Set}
   -> ((x : [ S ]F) -> T x)
   -> S -F> T
\\F {`[ N ]} f = < \\E f >
\\F {R `>< S} f = < (\\F \ r -> \\F \ s -> f (r , s)) >

_$F_ : {S : UF}{T : [ S ]F -> Set}
   -> S -F> T
   -> ((x : [ S ]F) -> T x)
_$F_ {`[ N ]} < k > x = k $E x
_$F_ {R `>< S} < k > (r , s) = k $F r $F s

infixl 30 _$F_

betaF : {S : UF}{T : [ S ]F -> Set}
   -> (f : (x : [ S ]F) -> T x)
   -> (x : [ S ]F) -> (\\F f $F x) ~ f x
betaF {`[ ts ]} f x = betaE f x
betaF {R `>< S} f (r , s) = 
  (\\F \ r -> \\F \ s -> f (r , s)) $F r $F s
     ~[ (_$F s) $~ betaF (\ r -> \\F \ s -> f (r , s)) r >
  (\\F \ s -> f (r , s)) $F s
    ~[ betaF (\ s -> f (r , s)) s >
  f (r , s) [QED]

-- HERE: extF isn't just for lambdas?
-- what's the right mix of extF and etaF
extF : {S : UF}{T : [ S ]F -> Set}
    -> (f g : (x : [ S ]F) -> T x)
    -> ((x : [ S ]F) -> f x ~ g x)
    -> \\F f ~ \\F g
extF {`[ ts ]} f g q = <_> $~ extE f g q
extF {S `>< T} f g q = <_> $~
  extF _ _ \ r -> extF _ _ \ s -> q (r , s)

etaF : {S : UF}{T : [ S ]F -> Set}
    -> (k : S -F> T)
    -> (\\F \ i -> k $F i) ~ k
etaF {`[ ts ]} < k > = <_> $~ etaE k
etaF {R `>< S} < k > = <_> $~ (
  (\\F \ r -> \\F \ s -> k $F r $F s)
    ~[ extF _ _ (\ r -> etaF (k $F r)) >
  \\F (_$F_ k)
    ~[ etaF k >
  k [QED])


infix 20 _<|_
record Fontainer : Set where
  constructor _<|_
  field
    Sh : UF
    Po : [ Sh ]F -> UF
open Fontainer

infix 15 [_]^F
[_]^F : Fontainer -> Set -> Set
[ S <| P ]^F X = [ S ]F >< \ s -> P s -F> \ _ -> X

data _^*_ (C : Fontainer)(X : Set) : Set where
  #   : X -> C ^* X
  <_> : [ C ]^F (C ^* X) -> C ^* X

data Problem : Set where
  base : Problem
  _-F<_ : (S : UF)(P : [ S ]F -> Problem) -> Problem
  _-E<_ : (S : UE)(P : [ S ]E -> Problem) -> Problem

module _ {C : Fontainer} where

  module _ {X : Set} where
  
    data Rec : C ^* X -> Set where
      # : forall x -> Rec (# x)
      step : (s : [ C .Sh ]F)
         -> forall {k}
         -> (f : (p : [ C .Po s ]F) -> Rec (_$F_ {C .Po s} k p))
         -> Rec < s , k >

    Input : Problem -> Set
    Input base = C ^* X
    Input (S -F< P) = S -F> \ s -> Input (P s)
    Input (S -E< P) = S -E> \ s -> Input (P s)

    Output : (P : Problem) -> Input P -> Set
    Output base t = Rec t
    Output (S -F< P) k = (s : [ S ]F) ->
      Output (P s) (k $F s)
    Output (S -E< P) k = (s : [ S ]E) ->
      Output (P s) (k $E s)

    solve : (P : Problem)(i : Input P) -> Output P i
    
    solve base (# x) = # x
    solve base < s , k > = step s
      (solve (C .Po s -F< (\ _ -> base)) k)
      
    solve ((R `>< S) -F< P) < k > (r , s) =
      solve (R -F< \ r -> S r -F< \ s -> P (r , s)) k r s
    solve (`[ ts ] -F< P) < k > i =
      solve (ts -E< P) k i
      
    solve ([] -E< P) i (_ , ())
    solve ((t ,- ts) -E< P) < z , k > zee =
      solve (P zee) z
    solve ((t ,- ts) -E< P) < z , k > (suu i) =
      solve (ts -E< (sus - P)) k (_ , i)

    rec = solve base

joinr : forall {C X} -> (xcc : C ^* (C ^* X)) -> Rec xcc -> C ^* X
joinr (# t) (# t) = t
joinr < s , k > (step s f) =
  < s , (\\F \ p -> joinr (k $F p) (f p)) >

join : forall {C X} -> C ^* (C ^* X) -> C ^* X
join xcc = joinr xcc (rec xcc)

{-
Working towards the join laws, we introduce a slightly asymmetric
version of the C ^_ relator.
  [_]^*_<=_ (R : A -> C ^* B -> Set)
    : C ^* A -> C ^* B -> Set 
This lifts
a relation R between A-variables and B-terms to
a relation between A-terms and B-terms
by insisting that the latter have the same node structure
as the former, and that the A-variable leaves in the former
are related to the corresponding B-subterms in the latter.

In particular, the Join relation is a special case
  _-Join-_ : C ^* (C ^* A) -> C ^* A -> Set
  acc -Join- ac = [ _~_ ]^* acc <= ac 
-}

module _ {C : Fontainer} where

 module _ {A B : Set} where

  --
  data [_]^*_<=_ (R : A -> C ^* B -> Set)
    : C ^* A -> C ^* B -> Set where
    # : forall {a b} -> R a b -> [ R ]^* # a <= b
    step : forall s {j k}
        -> ((p : [ C .Po s ]F) -> [ R ]^* (j $F p) <= (k $F p))
        -> [ R ]^* < s , j > <= < s , k >

  module _ (R : A -> B -> Set) where

    {- We recover the usual relator by saying
       when a B-term is a related B-variable.
    -}
    data R# (a : A) : C ^* B -> Set where
      [_]# : {b : B} -> R a b -> R# a (# b)

    [_]^*_<->_ : C ^* A -> C ^* B -> Set
    [_]^*_<->_ ac bc = [ R# ]^* ac <= bc

 module _ {A : Set} where

  diag : (ac : C ^* A) -> [ _~_ ]^* ac <-> ac
  diag = rec - go where
    go : forall {ac} -> Rec ac -> [ _~_ ]^* ac <-> ac
    go (# x) = # [ r~ ]#
    go (step s f) = step s \ p -> go (f p)

 module _ {A B : Set} where
  module _
    {R : A -> C ^* B -> Set}
    {S : A -> C ^* B -> Set}
    (rs : forall {a bc} -> R a bc -> S a bc)
    where

    MAPR : forall {ac bc} -> [ R ]^* ac <= bc -> [ S ]^* ac <= bc
    MAPR (# r) = # (rs r)
    MAPR (step s f) = step s \ p -> MAPR (f p)

  module _ {R S : A -> B -> Set}(rs : forall {a b} -> R a b -> S a b) where
    -- is the type of rs too tight?

    MAPR# : forall {ac bc} -> [ R ]^* ac <-> bc -> [ S ]^* ac <-> bc
    MAPR# = MAPR \ { [ r ]# -> [ rs r ]# }

  module _ (R : A -> C ^* B -> Set)(abc : (a : A) -> <: R a :>) where

    shtep : (s : [ C .Sh ]F)(k : C .Po s -F> (\ _ -> C ^* A))
         -> ((p : [ C .Po s ]F) -> <: [ R ]^* (k $F p) <=_ :>)
         -> <: [ R ]^* < s , k > <=_ :>
    shtep s k h
      = < s , (\\F \ p -> fst (h p)) >
      , step s \ p -> tsbus _ _ (betaF (\ p -> h p .fst) p) ([ R ]^* k $F p <=_) (h p .snd)
                  --  ^^^^^ it's tricky to get rid of this

    -- what's new here is the need to *construct* the related term
    -- can't do that just by relation implication

    mapRr : (ac : C ^* A) -> Rec ac -> <: [ R ]^* ac <=_ :>
    mapRr (# _) (# x) with _ , r <- abc x = _ , # r
    mapRr < s , k > (step s f) = shtep s k \ p -> mapRr _ (f p)

    mapR : (ac : C ^* A) -> <: [ R ]^* ac <=_ :>
    mapR ac = mapRr ac (rec ac)

  module _ (R : A -> C ^* B -> Set)(aq : forall {a b0 b1} -> R a b0 -> R a b1 -> b0 ~ b1)
    where

    funR : forall {ac bc0 bc1}
        -> [ R ]^* ac <= bc0
        -> [ R ]^* ac <= bc1
        -> bc0 ~ bc1
    funR (# rab0) (# rab1) = aq rab0 rab1
    funR (step s {k = j} f) (step .s {k = k} g) = ((s ,_) - <_>) $~ (
      j
      < etaF j ]~
      (\\F \ p -> j $F p)
      ~[ extF _ _ (\ p -> funR (f p) (g p)) >
      (\\F \ p -> k $F p)
      ~[ etaF k >
      k [QED])

 module _ {A B : Set}{R : A -> B -> Set} where

  sym^* : forall {ac bc}
       -> [ R ]^* ac <-> bc
       -> [ (\ b a -> R a b) ]^* bc <-> ac
  sym^* (# [ x ]#) = # [ x ]#
  sym^* (step s f) = step s \ p -> sym^* (f p)


 module _ {A B D : Set}
    {R : A -> C ^* B -> Set}{S : B -> C ^* D -> Set} where

   _-^*-_ : forall {ac bc dc}
     -> [ R ]^* ac <= bc
     -> [ S ]^* bc <= dc
     -> [ R -Rel- [_]^*_<=_ S ]^* ac <= dc
   # ab -^*- bd = # (_ , ab , bd)
   step s f -^*- step .s g = step s \ p -> f p -^*- g p

 module _ {A B D : Set}{R : A -> B -> Set}{S : B -> D -> Set} where

   _-^*#-_ : forall {ac bc dc}
     -> [ R ]^* ac <-> bc
     -> [ S ]^* bc <-> dc
     -> [ R -Rel- S ]^* ac <-> dc
   ab -^*#- bd = MAPR (\ { (_ , [ r ]# , # [ s ]#) -> [ _ , r , s ]# }) (ab -^*- bd)
   

 module _ {A : Set} where

  map : forall {B} -> (A -> B) -> C ^* A -> C ^* B
  map ab ac = fst (mapR (R# \ a b -> ab a ~ b) (\ a -> _ , [ r~ ]#) ac)

  liftR~ : {ac bc : C ^* A} -> [ _~_ ]^* ac <-> bc -> ac ~ bc
  liftR~ (# [ r~ ]#) = r~
  liftR~ (step s {j} {k} f) = ((s ,_) - <_>) $~ (
      j
      < etaF j ]~
      (\\F \ p -> j $F p)
      ~[ extF _ _ (\ p -> liftR~ (f p)) >
      (\\F \ p -> k $F p)
      ~[ etaF k >
      k [QED])

  lift~R : (ac : C ^* A) -> [ _~_ ]^* ac <-> ac
  lift~R ac
    with bc , abcq <- mapR (R# _~_) (\ a -> _ , [ r~ ]#) ac
    with r~ <- liftR~ abcq
    = abcq

  mapId : forall (aa : A -> A)
     -> (q : (a : A) -> aa a ~ a)
     -> (ac : C ^* A)
     -> map aa ac ~ ac
  mapId aa q ac
    with bc , abcq <- mapR (R# \ a b -> aa a ~ b) (\ a -> _ , [ r~ ]#) ac
       = bc
           < liftR~ (MAPR (\ { {a} [ r~ ]# -> [ a < q a ]~ aa a [QED] ]# }) abcq) ]~
         ac [QED]

  _-Join-_ : C ^* (C ^* A) -> C ^* A -> Set
  acc -Join- ac = [ _~_ ]^* acc <= ac 

 module _ {R S T}
   {rs : R -> S}{st : S -> T}{rt : R -> T}
   (q : (r : R) -> st (rs r) ~ rt r)
   (rc : C ^* R)
   where
   

    mapCo : map st (map rs rc) ~ map rt rc
    mapCo
      with sc , rscq <- mapR (R# \ a b -> rs a ~ b) (\ a -> _ , [ r~ ]#) rc
         | tc1 , rtcq <- mapR (R# \ a b -> rt a ~ b) (\ a -> _ , [ r~ ]#) rc
      with tc0 , stcq <- mapR (R# \ a b -> st a ~ b) (\ a -> _ , [ r~ ]#) sc
      = liftR~
          (MAPR (\ { [ _ , (_ , r~ , r~) , r~ ]# -> [ q _ ]# })
                (sym^* (rscq -^*#- stcq) -^*#- rtcq))



{- -- KEEP THIS (ELSEWHERE?) IT'S GLORIOUSLY GHASTLY!
mapr : forall {C A B} -> (A -> B)
    -> (ac : C ^* A) -> Rec ac -> C ^* B
mapr ab (# a) (# .a) = # (ab a)
mapr ab < s , k > (step s f) =
  < s , (\\F \ p -> mapr ab (k $F p) (f p)) >

map : forall {C A B} -> (A -> B) -> C ^* A -> C ^* B
map ab ac = mapr ab ac (rec ac)

mapIdR : forall {C A}(aa : A -> A)
      -> (q : (a : A) -> aa a ~ a)
      -> (ac : C ^* A)(acr : Rec ac)
      -> mapr aa ac acr ~ ac
mapIdR aa q ac (# a) = # $~ q a
mapIdR aa q ac (step s {k} f) = ((s ,_) - <_>) $~ (
  (\\F \ p -> mapr aa (k $F p) (f p))
    ~[ extF _ _ (\ p -> mapIdR aa q _ _) >
  \\F (_$F_ k)
    ~[ etaF k >
  k [QED])

mapId : forall {C A}(aa : A -> A)
     -> (q : (a : A) -> aa a ~ a)
     -> (ac : C ^* A)
     -> map aa ac ~ ac
mapId aa q ac = mapIdR aa q ac (rec ac)

mapExtR : forall {C R S}
  {j l : R -> S}
  (q : (r : R) -> j r ~ l r)
  (rc : C ^* R)(rj : Rec rc)
  (rd : C ^* R)(rl : Rec rd)
  (w : rc ~ rd)
  ->
  mapr j rc rj ~ mapr l rd rl
mapExtR q (# x) (# .x) (# .x) (# .x) r~ = # $~ q x
mapExtR {j = j}{l} q < (s , k) > (step s f) < (s , k) > (step .s g) r~
  = ((s ,_) - <_>) $~ (
  (\\F \ p -> mapr j (k $F p) (f p))
    ~[ extF _ _ (\ p -> mapExtR q (k $F p) (f p) (k $F p) (g p) r~) >
  (\\F \ p -> mapr l (k $F p) (g p))
    [QED])

mapCoR : forall {C R S T}
  {rs : R -> S}{st : S -> T}{rt : R -> T}
  (q : (r : R) -> st (rs r) ~ rt r)
  (rc : C ^* R)(rcr : Rec rc)
  (scr : Rec (mapr rs rc rcr))
  ->
  mapr st (mapr rs rc rcr) scr ~ mapr rt rc rcr
mapCoR q (# x) (# .x) (# _) = # $~ q x
mapCoR {rs = rs}{st}{rt} q < (s , k) > (step .s f) (step .s g) =
  ((s ,_) - <_>) $~ (
  (\\F \ p -> mapr st ((\\F \ p -> mapr rs (k $F p) (f p)) $F p) (g p))
    ~[ extF _ _ (\ p -> mapExtR (\ _ -> r~) _ _ _ _
                          (betaF (\ p -> mapr rs (k $F p) (f p)) p)) >
  (\\F \ p -> mapr st (mapr rs (k $F p) (f p)) _)
    ~[ extF _ _ (\ p -> mapCoR q (k $F p) (f p)
        (subst _ _ (betaF (\ p -> mapr rs (k $F p) (f p)) p) Rec (g p))) >
  (\\F \ p -> mapr rt (k $F p) (f p))
    [QED])

mapCo : forall {C R S T}
  {rs : R -> S}{st : S -> T}{rt : R -> T}
  (q : (r : R) -> st (rs r) ~ rt r)
  (rc : C ^* R)
  ->
  map st (map rs rc) ~ map rt rc
mapCo q rc = mapCoR q rc (rec rc) (rec (mapr _ rc (rec rc)))
-}
