module DataEqDec where

open import String

open import Basics
open import Thinnings
open import Membership
open import Finite
open import TabulatedFunctions
open import Universes
open import FiniteEq
open import Equality


-- Should this be indexed over a position set and pack functions from positions *inside*?
data PoStack (Ix : U Extensional) : Set where
  poNil : El Ix -> PoStack Ix
  poCons : (S : UF)(T : ElF S -> PoStack Ix) -> PoStack Ix

-----------------------------------------------------------------------------------
-- The next gazillions of lines help us show that we have decidable equality for the universe
-- of Data.
EqDec : (T0 : U Data)(t0 : El T0)(T1 : U Data)(t1 : El T1) -> Decision UPROPS
EnumDec : (xs ys : List String)(D : <: _-in xs :> -> <: _-in ys :> -> Decision UPROPS) -> Decision UPROPS
TabDec : (S0 : UF)(S1 : UF) -> (ElF S0 -> ElF S1 -> Decision UPROPS) -> Decision UPROPS

EnumDec xs ys D .Naw = (Enum-Rel xs ys \ xi yj -> D xi yj . Aye) `=> `0
EnumDec xs ys D .Aye = Enum-Rel xs ys \ xi yj -> D xi yj . Aye
EnumDec [] [] D .decide = `1 , _
EnumDec [] (x ,- ys) D .decide = `1 , _
EnumDec (x ,- xs) [] D .decide = `1 , _
EnumDec (x ,- xs) (y ,- ys) D .decide with D (x , ze) (y , ze) .decide
... | `0 , r = `0 , \ (z , _) -> D (x , ze) (y , ze) .exclude r z
... | `1 , q with EnumDec xs ys (\ (_ , i) (_ , j) -> D (_ , su i) (_ , su j)) .decide
... | `0 , r = `0 , \ (_ , s) -> EnumDec xs ys (\ (_ , i) (_ , j) -> D (_ , su i) (_ , su j)) .exclude r s
... | `1 , r = `1 , q , r
EnumDec xs ys D .exclude naw aye = naw aye

TabDec S0 S1 D .Naw = ElF-Rel S0 S1 (\ s0 s1 -> D s0 s1 .Aye) `=> `0
TabDec S0 S1 D .Aye = ElF-Rel S0 S1 (\ s0 s1 -> D s0 s1 .Aye)
TabDec (S0 `>< T0) (S1 `>< T1) D .decide =
  TabDec S0 S1 (\ s0 s1 -> TabDec (T0 s0) (T1 s1) \ t0 t1 -> D (s0 , t0) (s1 , t1))
  .decide
TabDec (S0 `>< T) `0 D .decide = `1 , _
TabDec (S0 `>< T) `1 D .decide = `1 , _
TabDec (S0 `>< T) (`E x) D .decide = `1 , _
TabDec `0 (S1 `>< T) D .decide = `1 , _
TabDec `0 `0 D .decide = `1 , _
TabDec `0 `1 D .decide = `1 , _
TabDec `0 (`E x) D .decide = `1 , _
TabDec `1 (S1 `>< T) D .decide = `1 , _
TabDec `1 `0 D .decide = `1 , _
TabDec `1 `1 D .decide with D <> <> .decide   -- sheer kludgery
... | `0 , r = `0 , D <> <> .exclude r
... | `1 , r = `1 , r
TabDec `1 (`E x) D .decide = `1 , _
TabDec (`E x) (S1 `>< T) D .decide = `1 , _
TabDec (`E x) `0 D .decide = `1 , _
TabDec (`E x) `1 D .decide = `1 , _
TabDec (`E xs) (`E ys) D .decide = EnumDec xs ys D .decide
TabDec S0 S1 D .exclude naw aye = naw aye

{-
TabDec : (S0 : UF)(T0 : ElF S0 -> U Data)(f0 : S0 #> (T0 - El))
         (S1 : UF)(T1 : ElF S1 -> U Data)(f1 : S1 #> (T1 - El))
      -> Decision
-- Naw and Aye are forced by the use site
TabDec S0 T0 f0 S1 T1 f1 .Naw = _
TabDec S0 T0 f0 S1 T1 f1 .Aye = _
TabDec (R0 `>< S0) T0 f0 (R1 `>< S1) T1 f1 .decide = {!!}
-- ... but it doesn't lift neatly through the currying-out of the `><
-}

EqDec T0 t0 T1 t1 .Naw = Eq T0 t0 T1 t1 `=> `0
EqDec T0 t0 T1 t1 .Aye = Eq T0 t0 T1 t1

-- signals on the diagonal
EqDec (S0 `>< T0) (s0 , t0) (S1 `>< T1) (s1 , t1) .decide with EqDec S0 s0 S1 s1 .decide
... | `0 , r = `0 , fst - r
... | `1 , q with EqDec (T0 s0) t0 (T1 s1) t1 .decide
... | `0 , r = `0 , snd - r
... | `1 , r = `1 , q , r

EqDec `1 <> `1 <> .decide = `1 , _

EqDec (S0 `#>> T0) f0 (S1 `#>> T1) f1 .decide =
  (TabDec S0 S1 \ s0 s1 -> EqDec (T0 s0) (ffapp S0 f0 s0) (T1 s1) (ffapp S1 f1 s1)) .decide

EqDec (`E xs) xi (`E ys) yj .decide = Enum-EqDec xs xi ys yj .decide

EqDec (`List T0) t0s (`List T1) t1s .decide = listEq? t0s t1s where
  listEq? : (t0s : El (`List T0))(t1s : El (`List T1)) ->
    el UPROPS (EqDec (`List T0) t0s (`List T1) t1s .Naw) +
    el UPROPS (EqDec (`List T0) t0s (`List T1) t1s .Aye)
  listEq? [] [] = `1 , _
  listEq? [] (t1 ,- t1s) = `0 , id
  listEq? (t0 ,- t0s) [] = `0 , id
  listEq? (t0 ,- t0s) (t1 ,- t1s) with EqDec T0 t0 T1 t1 .decide | listEq? t0s t1s
  ... | `0 , p | b , q = `0 , \ (x , _) -> p x
  ... | `1 , p | `0 , q = `0 , \ (_ , x) -> q x
  ... | `1 , p | `1 , q = `1 , p , q

EqDec (`Mu Ix0 Sh0 Pos0 posix0 i0) t0 (`Mu Ix1 Sh1 Pos1 posix1 i1) t1 .decide
  = poStkEq? (poNil i0) t0 (poNil i1) t1 where
  {- Seems like what we want, but we generalize it (below)
     and make more of it transparently (to Agda) first-order while
     at it.

  -- HERE: refactor using MuRec

  muEq? : (i0 : El Ix0) (t0 : El (`Mu Ix0 Sh0 Pos0 posix0 i0))
          (i1 : El Ix1) (t1 : El (`Mu Ix1 Sh1 Pos1 posix1 i1))
       ->
        el UPROPS
        (EqDec (`Mu Ix0 Sh0 Pos0 posix0 i0) t0 (`Mu Ix1 Sh1 Pos1 posix1 i1)
         t1 .Naw)
        +
        el UPROPS
        (EqDec (`Mu Ix0 Sh0 Pos0 posix0 i0) t0 (`Mu Ix1 Sh1 Pos1 posix1 i1)
         t1 .Aye)
  -}

  elPoS0 : PoStack Ix0 -> U Data
  elPoS0 (poNil i0) = `Mu Ix0 Sh0 Pos0 posix0 i0
  elPoS0 (poCons S T) = S `#>> \ s -> elPoS0 (T s)

  elPoS1 : PoStack Ix1 -> U Data
  elPoS1 (poNil i1) = `Mu Ix1 Sh1 Pos1 posix1 i1
  elPoS1 (poCons S T) = S `#>> \ s -> elPoS1 (T s)

  poStkEq? : (p0 : PoStack Ix0) (t0 : El (elPoS0 p0))(p1 : PoStack Ix1) (t1 : El (elPoS1 p1))
          ->  El (Eq (elPoS0 p0) t0 (elPoS1 p1) t1 `=> `0)
           +  El (Eq (elPoS0 p0) t0 (elPoS1 p1) t1)
  
  kEq? : (P0 : UF)(pstk0 : ElF P0 -> PoStack Ix0) -- can we hide this function inside PoStack?
         (k0 : P0 #> (pstk0 - elPoS0 - El))
         (P1 : UF)(pstk1 : ElF P1 -> PoStack Ix1)
         (k1 : P1 #> (pstk1 - elPoS1 - El))
    -> el UPROPS (ElF-Rel P0 P1 (\ p0 p1 -> EqDec
          (elPoS0 (pstk0 p0)) (ffapp P0 k0 p0)
          (elPoS1 (pstk1 p1)) (ffapp P1 k1 p1)
        .Aye) `=> `0)
     + el UPROPS (ElF-Rel P0 P1 \ p0 p1 -> EqDec
          (elPoS0 (pstk0 p0)) (ffapp P0 k0 p0)
          (elPoS1 (pstk1 p1)) (ffapp P1 k1 p1)
        .Aye)
  tupEq? : ∀ xs0 (pstk0 : ElF (`E xs0) → PoStack Ix0)
           (k0 : `E xs0 #>' (pstk0 - elPoS0 - El)) xs1
           (pstk1 : ElF (`E xs1) → PoStack Ix1)
           (k1 : `E xs1 #>' (pstk1 - elPoS1 - El)) →
         el UPROPS
         (ElF-Rel (`E xs0) (`E xs1)
          (λ p0 p1 →
             EqDec (elPoS0 (pstk0 p0)) (ffapp (`E xs0) < k0 > p0)
             (elPoS1 (pstk1 p1)) (ffapp (`E xs1) < k1 > p1) .Aye)
          `=> `0)
         +
         el UPROPS
         (ElF-Rel (`E xs0) (`E xs1)
          (λ p0 p1 →
             EqDec (elPoS0 (pstk0 p0)) (ffapp (`E xs0) < k0 > p0)
             (elPoS1 (pstk1 p1)) (ffapp (`E xs1) < k1 > p1) .Aye))

  poStkEq? (poNil _) _ (poCons _ _) _ = `1 , _
  poStkEq? (poCons _ _) _ (poNil _) _ = `1 , _
  
  poStkEq? (poCons S0 T0) k0 (poCons S1 T1) k1 =
    kEq? S0 T0 k0 S1 T1 k1

  poStkEq? (poNil i0) (con s0 k0) (poNil i1) (con s1 k1) with EqDec (Sh0 i0) s0 (Sh1 i1) s1 .decide
  ... | `0 , p = `0 , \ (x , _) -> p x
  ... | `1 , p
    with kEq? (Pos0 i0 s0) (posix0 i0 s0 - poNil) k0 (Pos1 i1 s1) (posix1 i1 s1 - poNil) k1
  ... | `0 , q = `0 , \ (_ , x) -> q x
  ... | `1 , q = `1 , p , q


  kEq? (S0 `>< T0) pstk0 k0 `0 pstk1 k1 = `1 , _
  kEq? (S0 `>< T0) pstk0 k0 `1 pstk1 k1 = `1 , _
  kEq? (S0 `>< T0) pstk0 k0 (`E x) pstk1 k1 = `1 , _
  kEq? `0 pstk0 k0 (P1 `>< T) pstk1 k1 = `1 , _
  kEq? `0 pstk0 k0 `1 pstk1 k1 = `1 , _
  kEq? `0 pstk0 k0 (`E x) pstk1 k1 = `1 , _
  kEq? `1 pstk0 k0 (P1 `>< T) pstk1 k1 = `1 , _
  kEq? `1 pstk0 k0 `0 pstk1 k1 = `1 , _
  kEq? `1 pstk0 k0 (`E x) pstk1 k1 = `1 , _
  kEq? (`E x) pstk0 k0 (P1 `>< T) pstk1 k1 = `1 , _
  kEq? (`E x) pstk0 k0 `0 pstk1 k1 = `1 , _
  kEq? (`E x) pstk0 k0 `1 pstk1 k1 = `1 , _

  -- here is the same problem as with TabDec Mk I
  -- k0 has an S0 outer layer whose children are not Mus, but rather T0s of Mus
  kEq? (S0 `>< T0) pstk0 < k0 > (S1 `>< T1) pstk1 < k1 > = 
    kEq? S0 (\ s0 -> poCons (T0 s0) \ t0 -> pstk0 (s0 , t0)) k0
         S1 (\ s1 -> poCons (T1 s1) \ t1 -> pstk1 (s1 , t1)) k1
  
  kEq? `0 pstk0 k0 `0 pstk1 k1 = `1 , _
  
  kEq? `1 pstk0 < t0 > `1 pstk1 < t1 > = poStkEq? (pstk0 <>) t0 (pstk1 <>) t1
  
  kEq? (`E xs0) pstk0 < k0 > (`E xs1) pstk1 < k1 > = tupEq? xs0 pstk0 k0 xs1 pstk1 k1
  
  tupEq? [] pstk0 k0 [] pstk1 k1 = `1 , _
  tupEq? [] pstk0 k0 (x ,- xs1) pstk1 k1 = `1 , _
  tupEq? (x ,- xs0) pstk0 k0 [] pstk1 k1 = `1 , _
  tupEq? (x0 ,- xs0) pstk0 (t0 , k0) (x1 ,- xs1) pstk1 (t1 , k1)
    with poStkEq? (pstk0 (_ , ze)) t0 (pstk1 (_ , ze)) t1
       | tupEq? xs0 (\ (_ , i) -> pstk0 (_ , su i)) k0 xs1 (\ (_ , i) -> pstk1 (_ , su i)) k1
  ... | `0 , q | c , r = `0 , fst - q
  ... | `1 , q | `0 , r = `0 , snd - r
  ... | `1 , q | `1 , r = `1 , q , r
  
EqDec (`Prf _) _ (`Prf _) _ .decide = `1 , _

-- noises off
EqDec (_ `>< _) _ `1 _ .decide = `1 , _
EqDec (_ `>< _) _ (_ `#>> _) _ .decide = `1 , _
EqDec (_ `>< _) _ (`E _) _ .decide = `1 , _
EqDec (_ `>< _) _ (`List _) _ .decide = `1 , _
EqDec (_ `>< _) _ (`Mu _ _ _ _ _) _ .decide = `1 , _
EqDec (_ `>< _) _ (`Prf _) _ .decide = `1 , _
EqDec `1 _ (_ `>< _) _ .decide = `1 , _
EqDec `1 _ (_ `#>> _) _ .decide = `1 , _
EqDec `1 _ (`E _) _ .decide = `1 , _
EqDec `1 _ (`List _) _ .decide = `1 , _
EqDec `1 _ (`Mu _ _ _ _ _) _ .decide = `1 , _
EqDec `1 _ (`Prf _) _ .decide = `1 , _
EqDec (_ `#>> _) _ (_ `>< _) _ .decide = `1 , _
EqDec (_ `#>> _) _ `1 _ .decide = `1 , _
EqDec (_ `#>> _) _ (`E _) _ .decide = `1 , _
EqDec (_ `#>> _) _ (`List _) _ .decide = `1 , _
EqDec (_ `#>> _) _ (`Mu _ _ _ _ _) _ .decide = `1 , _
EqDec (_ `#>> _) _ (`Prf _) _ .decide = `1 , _
EqDec (`E _) _ (_ `>< _) _ .decide = `1 , _
EqDec (`E _) _ `1 _ .decide = `1 , _
EqDec (`E _) _ (_ `#>> _) _ .decide = `1 , _
EqDec (`E _) _ (`List _) _ .decide = `1 , _
EqDec (`E _) _ (`Mu _ _ _ _ _₁) _ .decide = `1 , _
EqDec (`E _) _ (`Prf _) _ .decide = `1 , _
EqDec (`List _) _ (_ `>< _) _ .decide = `1 , _
EqDec (`List _) _ `1 _ .decide = `1 , _
EqDec (`List _) _ (_ `#>> _) _ .decide = `1 , _
EqDec (`List _) _ (`E _) _ .decide = `1 , _
EqDec (`List _) _ (`Mu _ _ _ _ _) _ .decide = `1 , _
EqDec (`List _) _ (`Prf _) _ .decide = `1 , _
EqDec (`Mu _ _ _ _ _) _ (_ `>< _) _ .decide = `1 , _
EqDec (`Mu _ _ _ _ _) _ `1 _ .decide = `1 , _
EqDec (`Mu _ _ _ _ _) _ (_ `#>> _) _ .decide = `1 , _
EqDec (`Mu _ _ _ _ _) _ (`E _) _ .decide = `1 , _
EqDec (`Mu _ _ _ _ _) _ (`List _) _ .decide = `1 , _
EqDec (`Mu _ _ _ _ _) _ (`Prf _) _ .decide = `1 , _
EqDec (`Prf _) _ (_ `>< _) _ .decide = `1 , _
EqDec (`Prf _) _ `1 _ .decide = `1 , _
EqDec (`Prf _) _ (_ `#>> _) _ .decide = `1 , _
EqDec (`Prf _) _ (`E _) _ .decide = `1 , _
EqDec (`Prf _) _ (`List _) _ .decide = `1 , _
EqDec (`Prf _) _ (`Mu _ _ _ _ _) _ .decide = `1 , _

EqDec T0 t0 T1 t1 .exclude naw aye = naw aye

-- End gazillion
-------------------------------------------------------------------------------
