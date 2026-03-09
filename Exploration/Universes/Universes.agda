module Universes where

open import String

open import Basics
open import Thinnings
open import Membership
open import Finite
open import TabulatedFunctions
open import Decided
open import Mu

data Content : Set where
  Value : Content
  Proof : Content
  
data Kind : Set where
    FO : Kind            -- first-order things
    HO : Content -> Kind -- higher-order things that has different content

-- what kinds embed in what other kinds?
data Embeds : Kind -> Kind -> Set where
  FO>HOV : Embeds FO (HO Value)
  HOP>FO : Embeds (HO Proof) FO
  -- don't need, derivable
  -- HOP>HOV : Embeds (HO Proof) (HO Value)

-- And now the polymorphic universes
data U : (k : Kind) -> Set
El : forall {k : Kind} -> U k -> Set

-- Convention: capital letters for big things
data U where
  -- All universes are closed under Sigma
  _`><_ : forall {k} -> (S : U k) -> (T : El S -> U k) -> U k

  -- only some universes have Zero and One
  `0 `1 : forall {k} -> U k

  -- Higher-order functions, only in the higher-order kinds!
  _`->_ : forall {c} -> (S : U (HO Value)) -> (T : El S -> U (HO c)) -> U (HO c)

  -- Tabulated functions
  _`#>>_ : (S : UF) -> (T : ElF S -> U FO) -> U FO

  -- enumerations
  `F : UF -> U FO

  -- fixed points (of indexed containers). For now, Finite positions.
  `Mu : forall {k} -> (Ix : U (HO Value)) -> (Sh : El Ix -> U k) ->
    (Pos : (i : El Ix) (s : El (Sh i)) -> UF) ->
    (posix : (i : El Ix) (s : El (Sh i)) (p : ElF (Pos i s)) -> El Ix) ->
    El Ix -> U k

  -- Making things out of proofs
  _`^_ : forall {j k} -> Embeds j k -> U j -> U k

infixr 30 _`->_

-- and all of this can be interpreted back into Agda
El (S `>< T) = El S >< \ s -> El (T s)
El `0 = Zero
El `1 = One
El (S `-> T) = (s : El S) -> El (T s)
El (S `#>> T) = S #> \ s -> El (T s)
El (`F E) = ElF E
El (`Mu Ix Sh Pos posix i) = Mu (El Ix) (\ i -> El (Sh i)) Pos posix i
El (_ `^ T) = El T

Types : Set
Types = U (HO Value)

Props : Set
Props = U (HO Proof)

pf=>vl : Props -> Types
pf=>vl p = FO>HOV `^ (HOP>FO `^ p)

uf=>vl : UF -> Types
uf=>vl d = FO>HOV `^ (`F d)

vl : forall {k} -> U k -> Types
vl {FO} T = FO>HOV `^ T
vl {HO Value} T = T
vl {HO Proof} T = pf=>vl T

pf : forall {k} -> Props -> U k
pf {FO} P = HOP>FO `^ P
pf {HO Value} P = vl P
pf {HO Proof} P = P

-- Some useful kit for (at least) proofs
infixr 20 _`/\_
_`/\_ : Props -> Props -> Props
P0 `/\ P1 = P0 `>< (kon P1)

infixr 20 _`=>_
_`=>_ : Props -> Props -> Props
P0 `=> P1 = pf=>vl P0 `-> (kon P1)

`NOT : Props -> Props
`NOT p = p `=> `0

-- decideds can be props
-- use De Morgan in a couple of spots (hide them bits!)
-- design decision: go all the way up to extensional for the
--  'function' buried under a negation
Forget : UD -> Props
Forget `0 = `0
Forget `1 = `1
Forget (D `| E) = `NOT (`NOT (Forget D) `/\ `NOT (Forget E))
Forget (D `& E) = Forget D `/\ Forget E
Forget (`Aa S D) = uf=>vl S `-> \ s -> Forget (D s)
Forget (`Ex S D) = `NOT (uf=>vl S `-> \ s -> `NOT (Forget (D s)))

forget : (D : UD) -> ElD D -> El (Forget D)
forget `1 <> = <>
forget (D `| E) (inl d) (nd , _) = nd (forget D d)
forget (D `| E) (inr e) (_ , ne) = ne (forget E e)
forget (D `& E) (d , e) = forget D d , forget E e
forget (`Aa S D) d s = forget (D s) (`ffapp S d s)
forget (`Ex S D) (s , d) bad = bad s (forget (D s) d)

-- Given an erased version, we can get classical double-negation
-- and then eventually recover the witness from that erased version
-- as everything in sight is decidable
RecallDNEG : (D : UD) -> El (Forget D) -> ((ElD D -> Zero) -> Zero)
Recall : (D : UD) -> El (Forget D) -> ElD D

RecallDNEG `1 pf denial = denial pf
RecallDNEG (D `| E) pf denial = pf ((\ d -> denial (inl (Recall D d))) ,
                                     \ e -> denial (inr (Recall E e)))
RecallDNEG (D `& E) (d , e) denial = denial (Recall D d , Recall E e)
RecallDNEG (`Aa S D) pf denial = denial (`fflam S (\ s -> Recall (D s) (pf s)) )
RecallDNEG (`Ex S D) pf denial = pf \s d -> denial (s , Recall (D s) d)

Recall D d = witnessDNEG D (RecallDNEG D d)

{-
HERE
4. The plan, then, is to show that Equality for U Data lives in UD.

-}
