module KleisliRelator where

open import Basics
--open import UE
open import UF
open import Fontainer

{-
joinr : forall {C X} -> (xcc : C ^* (C ^* X)) -> Rec xcc -> C ^* X
joinr (# t) (# t) = t
joinr < s , k > (step s f) =
  < s , (\\F \ p -> joinr (k $F p) (f p)) >

join : forall {C X} -> C ^* (C ^* X) -> C ^* X
join xcc = joinr xcc (rec xcc)
-}
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

  -- (name in lit.?)  We'll call it the "Kleisli relator"
  data [_]^*_<=_ (R : A -> C ^* B -> Set)
    : C ^* A -> C ^* B -> Set where
    # : forall {a b} -> R a b -> [ R ]^* # a <= b
    step : forall s {j k}
        -> ((p : [ C .Po s ]F) -> [ R ]^* (j $F p) <= (k $F p))
        -> [ R ]^* < s , j > <= < s , k >

  -- it has some useful properties we'll want to re-use

  -- if R is 'simple', so is its Kleisli relator
  module _ {R : A -> C ^* B -> Set}
           (simpR : forall {a bc0 bc1} ->  R a bc0 -> R a bc1 -> bc0 ~ bc1) where
    simpK : forall {ac bc0 bc1} -> ([ R ]^* ac <= bc0) -> ([ R ]^* ac <= bc1) ->
            bc0 ~ bc1
    simpK (# x) (# y) = simpR x y
    simpK (step s x0) (step .s x1) = ((s ,_) - <_>) $~ poiF (\ p -> simpK (x0 p) (x1 p))
    
  module _ (R : A -> B -> Set) where

    {- We recover the usual relator by saying
       when a B-term is a related B-variable.
    -}
    data R# (a : A) : C ^* B -> Set where
      [_]# : {b : B} -> R a b -> R# a (# b)

    [_]^*_<->_ : C ^* A -> C ^* B -> Set
    [_]^*_<->_ ac bc = [ R# ]^* ac <= bc

 module _ {A : Set} where

  module _ (R : A -> C ^* A -> Set) (reflR : (a : A) -> R a (# a)) where
    diagR : (ac : C ^* A) -> [ R ]^* ac <= ac
    diagR = rec - go where
      go : forall {ac} -> Rec ac -> [ R ]^* ac <= ac
      go (# x) = # (reflR x)
      go (step s f) = step s \ p -> go (f p)

  diag : (ac : C ^* A) -> [ _~_ ]^* ac <-> ac
  diag = diagR (R# _~_) \ _ -> [ r~ ]#


{- HERE
   The word "map" is used in too many incompatible ways.
   Let's try to tighten the naming.
-}

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

  -- note: in the special case where R is a function, this is 'bind'.
  module _ {R : A -> C ^* B -> Set}(abc : (a : A) -> <: R a :>) where

    shtep : (s : [ C .Sh ]F)(k : C .Po s -F> (\ _ -> C ^* A))
         -> ((p : [ C .Po s ]F) -> <: [ R ]^* (k $F p) <=_ :>)
         -> <: [ R ]^* < s , k > <=_ :>
    shtep s k h
      = < s , (\\F \ p -> h p .fst) >
      , step s \ p -> ford [ _ ]^* _ <=_ (_ , h p .snd , sym~ (betaF (\ p -> h p .fst) p))
                  --  ^^^^ it's tricky to get rid of this

    -- what's new here is the need to *construct* the related term
    -- can't do that just by relation implication

    entiKr : (ac : C ^* A) -> Rec ac -> <: [ R ]^* ac <=_ :>
    entiKr (# _) (# x) with _ , r <- abc x = _ , # r
    entiKr < s , k > (step s f) = shtep s k \ p -> entiKr _ (f p)

    -- if R is entire, so it its Kleisli relator
    entiK : (ac : C ^* A) -> <: [ R ]^* ac <=_ :>
    entiK ac = entiKr ac (rec ac)

 -- relational version of the Kleisli laws

 module _ {A B : Set}{R : A -> B -> Set} where

  -- Symmetry of relator lifts
  sym^* : forall {ac bc}
       -> [ R ]^* ac <-> bc
       -> [ (\ b a -> R a b) ]^* bc <-> ac
  sym^* (# [ x ]#) = # [ x ]#
  sym^* (step s f) = step s \ p -> sym^* (f p)


 module _ {A B D : Set}
    {R : A -> C ^* B -> Set}{S : B -> C ^* D -> Set} where

   -- composition of Kleisli relators
   _-^*-_ : forall {ac bc dc}
     -> [ R ]^* ac <= bc
     -> [ S ]^* bc <= dc
     -> [ R -Rel- [_]^*_<=_ S ]^* ac <= dc
   # ab -^*- bd = # (_ , ab , bd)
   step s f -^*- step .s g = step s \ p -> f p -^*- g p

 module _ {A B D : Set}{R : A -> B -> Set}{S : B -> D -> Set} where

   -- specializes
   _-^*#-_ : forall {ac bc dc}
     -> [ R ]^* ac <-> bc
     -> [ S ]^* bc <-> dc
     -> [ R -Rel- S ]^* ac <-> dc
   ab -^*#- bd = MAPR (\ { (_ , [ r ]# , # [ s ]#) -> [ _ , r , s ]# }) (ab -^*- bd)
   

 module _ {A : Set} where

  mapR : forall {B} -> (ab : A -> B) -> (ca : C ^* A) -> <: [ _[ ab >_ ]^* ca <->_ :>
  mapR ab ac = entiK {R = R# _[ ab >_} (\ a -> _ , [ r~ ]#) ac

  map : forall {B} -> (A -> B) -> C ^* A -> C ^* B
  map ab ac = fst (mapR ab ac)

  liftR~ : {ac bc : C ^* A} -> [ _~_ ]^* ac <-> bc -> ac ~ bc
  liftR~ (# [ r~ ]#) = r~
  liftR~ (step s {j} {k} f) = ((s ,_) - <_>) $~ poiF (\ p -> liftR~ (f p))

  lift~R : (ac : C ^* A) -> [ _~_ ]^* ac <-> ac
  lift~R ac
    with bc , abcq <- entiK (\ a -> _ , [ r~ ]#) ac
    with r~ <- liftR~ abcq
    = abcq

  mapId : forall (aa : A -> A)
     -> (q : (a : A) -> aa a ~ a)
     -> (ac : C ^* A)
     -> map aa ac ~ ac
  mapId aa q ac
    with bc , abcq <- entiK {R = R# \ a b -> aa a ~ b} (\ a -> _ , [ r~ ]#) ac
       = sym~ (liftR~ (MAPR (\ { {a} [ r~ ]# -> [ sym~ (q a) ]# }) abcq))

  -- join as a *relation*
  _-Join-_ : C ^* (C ^* A) -> C ^* A -> Set
  acc -Join- ac = [ _~_ ]^* acc <= ac 

  -- -Join- exist
  joinR : (acc : C ^* (C ^* A)) -> <: acc -Join-_ :>
  joinR = entiK \ _ -> _ , r~

  -- extract the given witness
  join : (acc : C ^* (C ^* A)) -> C ^* A
  join = joinR - fst

  -- join is left and right unital
  
  Join-lu : (ac : C ^* A) -> # ac -Join- ac
  Join-lu _ = # r~

  join-lu : (ac : C ^* A) -> join (# ac) ~ ac
  join-lu ac = r~

  Join-ru : {ac ac' : C ^* A}{acc : C ^* (C ^* A)}
    -> [ (\ a bc -> # a ~ bc) ]^* ac <-> acc
    -> acc -Join- ac'
    -> ac ~ ac'
  Join-ru x y = liftR~ (MAPR (\ { (_ , [ r~ ]# , # r~) -> [ r~ ]# }) (x -^*- y))

  join-ru : (ac : C ^* A) -> join (map # ac) ~ ac
  join-ru ac
    with acc , ac<->acc <- mapR {B = C ^* A} # ac
    with ac' , acc<->ac' <- joinR acc
    = sym~ (Join-ru ac<->acc acc<->ac')
  
 module _ {A : Set} where
  -- Relational version of associativity of join
  Join-assoc : {accc : C ^* (C ^* (C ^* A))}{acc bcc : C ^* (C ^* A)}{ac bc : C ^* A}
       -> accc -Join- acc -> acc -Join- ac
       -> [ _-Join-_ ]^* accc <-> bcc -> bcc -Join- bc
       -> ac ~ bc
  Join-assoc (# r~) h (# [ x ]#) (# r~) = simpK (\ { r~ q -> q }) h x
  Join-assoc (step s g) (step .s h) (step .s i) (step .s j) = ((s ,_) - <_>) $~
    poiF (\ p -> Join-assoc (g p) (h p) (i p) (j p))

  join-assoc : (accc : C ^* (C ^* (C ^* A))) ->
    join (join accc) ~ join (map join accc)
  join-assoc accc
    with acc , accc-acc <- joinR accc
    with bcc , accc-bcc <- mapR join accc
    with ac , acc-ac <- joinR acc
    with bc , bcc-bc <- joinR bcc =
      Join-assoc accc-acc acc-ac (MAPR# (\ { r~ → snd (joinR _)}) accc-bcc) bcc-bc

 module _ {R S T}
   {rs : R -> S}{st : S -> T}{rt : R -> T}
   (q : (r : R) -> st (rs r) ~ rt r)
   (rc : C ^* R)
   where
   
    mapCo : map st (map rs rc) ~ map rt rc
    mapCo
      with sc , rscq <- entiK {R = R# \ a b -> rs a ~ b} (\ _ -> _ , [ r~ ]#) rc
         | tc1 , rtcq <- entiK {R = R# \ a b -> rt a ~ b} (\ _ -> _ , [ r~ ]#) rc
      with tc0 , stcq <- entiK {R = R# \ a b -> st a ~ b} (\ _ -> _ , [ r~ ]#) sc
      = liftR~
          (MAPR (\ { [ _ , (_ , r~ , r~) , r~ ]# -> [ q _ ]# })
                (sym^* (rscq -^*#- stcq) -^*#- rtcq))


