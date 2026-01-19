module Universes where

open import String

open import Basics
open import Thinnings
open import Membership
open import Finite
open import TabulatedFunctions

data Kind : Set where
  Data         -- first-order data with decidable equality
    Extensional  -- higher-order stuff with behavioural equality
    Decided      -- proof-irrelevant and knowable
    Props        -- proof-irrelevant and interesting
    : Kind

-- only two of the universes can have extensional functions
canHazPi : Kind -> Set
canHazPi Extensional = One
canHazPi Props       = One
canHazPi _           = Zero

-- only some places have enumerations (Listable, really), namely not Props
canHazF : Kind -> Set
canHazF Decided = Zero
canHazF Props = Zero
canHazF _     = One

-- a couple of universes have (internal!!) lists
canHazList : Kind -> Set
canHazList Data = One
canHazList Extensional = One
canHazList _ = Zero

module _ (Ix : Set) (Sh : Ix -> Set) (Pos : (i : Ix) -> Sh i -> UF)
  (posix : (i : Ix) (s : Sh i) (p : ElF (Pos i s)) -> Ix)
  where

  data Mu  (i : Ix) : Set where
    con : (s : Sh i) -> (Pos i s #> \ p -> Mu (posix i s p)) -> Mu i

  data MuRec {i : Ix} : Mu i -> Set where
    con : (s : Sh i){k : Pos i s #> \ p -> Mu (posix i s p)}
       -> ((p : ElF (Pos i s)) -> MuRec (ffapp (Pos i s) k p))
       -> MuRec (con s k)

  data PoStack : Set where
    poNil : Ix -> PoStack
    poCons : (S : UF)(T : ElF S -> PoStack) -> PoStack

  ElPo : PoStack -> Set
  ElPo (poNil i) = Mu i
  ElPo (poCons S T) = S #> \ s -> ElPo (T s) 

  ElPoRec : (stk : PoStack) -> ElPo stk -> Set
  ElPoRec (poNil i) x = MuRec x
  ElPoRec (poCons S T) k = (s : ElF S) -> ElPoRec (T s) (ffapp S k s)  

  muRec : {i : Ix}(x : Mu i) -> MuRec x
  elPoRec : (p : PoStack)(x : ElPo p) -> ElPoRec p x
  muRecWork : (P : UF)(pstk : ElF P -> PoStack) (k : P #> (pstk - ElPo))
              (p : ElF P)
           -> ElPoRec (pstk p) (ffapp P k p)
  elPoTupRec : forall xs (pstk : ElF (`E xs) -> PoStack)
               (k : `E xs #> (pstk - ElPo)) (p : ElF (`E xs))
         ->  ElPoRec (pstk p) (ffapp (`E xs) k p)

  muRec {i} (con s k) = con s (muRecWork (Pos _ s) (posix _ s - poNil) k)
  elPoRec (poNil i) x = muRec x
  elPoRec (poCons S T) k = muRecWork S T k
  muRecWork (S `>< T) pstk < k > (s , t) = muRecWork S (\ s -> poCons (T s) \ t -> pstk (s , t)) k s t
  muRecWork `1 pstk < k > <> = elPoRec (pstk <>) k
  muRecWork (`E xs) pstk k p = elPoTupRec xs pstk k p
  elPoTupRec [] pstk k (_ , ())
  elPoTupRec (x ,- xs) pstk < j , _ > (_ , ze) = elPoRec (pstk zee) j
  elPoTupRec (x ,- xs) pstk < _ , k > (_ , su i) = elPoTupRec xs (suu - pstk) < k > (_ , i)

module _ {Ix : Set}{Sh0 Sh1 : Ix -> Set}(f : (i : Ix) -> Sh1 i -> Sh0 i)
       -- at every index we know how to transform 1-shapes into 0-shapes
       {Pos : (i : Ix) -> Sh0 i -> UF}
       {posix : (i : Ix) (s : Sh0 i) (p : ElF (Pos i s)) -> Ix}
  where

  shunWork : 
         {i : Ix}
         -- and now we extend that to Recursive data
      -> {x : Mu Ix Sh1 (\ i s1 -> Pos i (f i s1)) (\ i s1 p -> posix i (f i s1) p) i}
      -> MuRec _ _ _ _ x
      -> Mu Ix Sh0 Pos posix i
  shunWork (con sh xs) = con (f _ sh) (fflam (Pos _ (f _ sh)) \ p -> shunWork (xs p))

  shun : {i : Ix}
         -- and now we extend that to recursive data
      -> Mu Ix Sh1 (\ i s1 -> Pos i (f i s1)) (\ i s1 p -> posix i (f i s1) p) i
      -> Mu Ix Sh0 Pos posix i
  shun x = shunWork (muRec _ _ _ _ x)



-- And now the polymorphic universes
data U (k : Kind) : Set
El : forall {k : Kind} -> U k -> Set

-- Convention: capital letters for big things
data U k where
  -- All universes are closed under Sigma
  _`><_ : (S : U k) -> (T : El S -> U k) -> U k

  -- only some universes have Zero and One
  `0 `1 : U k

  -- Higher-order functions.
  _`->_ : {j : Kind} {_ : canHazPi k} -> (S : U j) -> (T : El S -> U k) -> U k

  -- Tabulated functions
  _`#>>_ : (S : UF) -> (T : ElF S -> U k) -> U k

  -- enumerations
  `F : {_ : canHazF k} -> UF -> U k

  -- lists
  `List : {_ : canHazList k} -> U k -> U k

  -- fixed points (of indexed containers). For now, Finite positions.
  `Mu : (Ix : U Extensional) -> (Sh : El Ix -> U k) ->
    (Pos : (i : El Ix) (s : El (Sh i)) -> UF) ->
    (posix : (i : El Ix) (s : El (Sh i)) (p : ElF (Pos i s)) -> El Ix) ->
    El Ix -> U k

  -- Making things out of proofs
  `Prf : U Props -> U k

  -- Negation for decision
  `Not : U Decided -> U k

El (S `>< T) = El S >< \ s -> El (T s)
El `0 = Zero
El `1 = One
El (S `-> T) = (s : El S) -> El (T s)
El (S `#>> T) = S #> \ s -> El (T s)
El (`F E) = ElF E
El (`List S) = List (El S)
El (`Mu Ix Sh Pos posix i) = Mu (El Ix) (\ i -> El (Sh i)) Pos posix i
El (`Prf P) = El P
El (`Not D) = El D -> Zero

-- Some useful kit for (at least) proofs
infixr 20 _`/\_
_`/\_ : U Props -> U Props -> U Props
P0 `/\ P1 = P0 `>< (kon P1)

_`=>_ : U Props -> U Props -> U Props
P0 `=> P1 = P0 `-> (kon P1)

_`->>_ : forall {k}{_ : canHazPi k} -> (S : U Extensional)(T : El S -> U k) -> U k
_`->>_ {k}{p} S T = _`->_ {k} {Extensional} {p} S T


-- could be made a constructor of U k, but is it worth the extra verbosity?
-- likewise, could generalize to any Universe, but we're unlikely to use that generality
`So : Two -> U Props
`So `0 = `0
`So `1 = `1

UFINITE UPROPS UDATA UEXTENSIONAL : Fam Set
UFINITE = fam UF ElF
UPROPS = fam (U Props) El
UDATA = fam (U Data) El
UEXTENSIONAL = fam (U Extensional) El

{-
-- We can embed UF types into U Data, but we need a backwards map
-- to cope with the dependency inherent in `><
F2D : (S : UF) -> U Data >< \ T -> El T -> ElF S
F2D (S `>< T) =
  let S' , f = F2D S in
  (S' `>< \ s' -> fst (F2D (T (f s')))) , \ (s' , t') ->
  let T' , g = F2D (T (f s')) in f s' , g t'
F2D `0 = `0 , \ ()
F2D `1 = `1 , _
F2D (`E xs) = `E xs , id
-}
{-
-- transport is tricky
f2d : (S : UF) -> let S' , f = F2D S
   in (s : ElF S)
   -> El S' >< \ s' -> El (EqF S s S (f s'))
f2d (S `>< T) (s , t) =
  let s' , sq = f2d S s in let t' , tq = f2d (T s) t in
  (s' , {!!}) , {!!}
f2d `1 s = _
f2d (`E xs) xi = xi , Enum-refl xs xi
-}

T2E : {k : Kind}(S : U k) -> U Extensional >< \ T -> El T -> El S
_^E : {k : Kind}(S : U k) -> U Extensional
S ^E = fst (T2E S)
_-E_ : {k : Kind}(S : U k) -> El (S ^E) -> El S
S -E s' = snd (T2E S) s'

T2E (S `>< T) = 
  let S' , f = T2E S in
  (S' `>< \ s' -> T (f s') ^E) , \ (s' , t') ->
  let T' , g = T2E (T (f s')) in f s' , g t'
T2E `0 = `0 , id
T2E `1 = `1 , id
T2E (S `-> T) = (S `-> \ s -> T s ^E) , \ f s -> T s -E f s
T2E (S `#>> T) = (S `#>> \ s -> T s ^E) , \ f -> fflam S \ s -> T s -E ffapp S f s
T2E (`F E) = `F E , id
T2E (`List S) = (`List >><< list) (T2E S)
T2E (`Mu Ix Sh Pos posix i)
  = `Mu Ix (\ i -> Sh i ^E) (\ i s' -> Pos i (Sh i -E s')) (\ i s' p -> posix i (Sh i -E s') p) i
  , shun (\ i -> Sh i -E_)
T2E (`Prf S) = `Prf S , id
T2E (`Not D) = `Not D , id

whatAbout : (D : U Decided) -> El {Decided} (`Not D) + El D
whoCares : (D : U Decided)(P : El D -> Set) (a b : El D) -> P a -> P b

whatAbout (D `>< T) with whatAbout D
... | `0 , x = `0 , fst - x
... | `1 , x with whatAbout (T x)
... | `0 , y = `0 , (/\ \ s t -> y (whoCares D _ s x t))
... | `1 , y = `1 , x , y
whatAbout `0 = `0 , id
whatAbout `1 = `1 , <>
whatAbout (S `#>> T) = {!!}
whatAbout (`Mu D Sh Pos posix x) = {!!}
whatAbout (`Prf D) = {!!}  -- make this not happen
whatAbout (`Not D) with whatAbout D
... | `0 , x = `1 , x
... | `1 , x = `0 , \ f -> f x

whoCares (S `>< T) P (as , at) (bs , bt) p =
  whoCares S (\ as -> (ct : El (T as)) -> P (as , ct)) as bs (\ ct -> whoCares (T as) _ at ct p) bt
whoCares `1 P <> <> p = p
whoCares (S `#>> T) P a b = {!!}
whoCares (`Mu D Sh Pos posix x) P a b p = {!!}
whoCares (`Prf D) P a b p = {!!}
whoCares (`Not D) P a b p = {!!} -- no chance, because P does not respect extensional equality!


{-
HERE
TODO

This was an attempt to introduce a universe of decided types.

1. This should allow `Prf.

2. Full `>< is getting us into gnarly coherence issues which push us to invent something like whoCares. Nondependent conjunction should be plenty.

3. Consider introducing a separate UD as we did with UF, then embedding everywhere with `D.

4. The plan, then, is to show that Equality for U Data lives in UD.

-}
