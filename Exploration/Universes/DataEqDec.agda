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
open import FiniteDecision

-----------------------------------------------------------------------------------
-- The next gazillions of lines help us show that we have decidable equality for the universe
-- of Data.
EqDec : (T0 : U Data)(t0 : El T0)(T1 : U Data)(t1 : El T1) -> Decision UPROPS
-- EnumDec : (xs ys : List String)(D : <: _-in xs :> -> <: _-in ys :> -> Decision UPROPS) -> Decision UPROPS
-- TabDec : (S0 : UF)(S1 : UF) -> (ElF S0 -> ElF S1 -> Decision UPROPS) -> Decision UPROPS

{-
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
TabDec S0 S1 D .Aye =
  S0 `#>> \ s0 -> S1 `#>> \ s1 -> EqF S0 s0 S1 s1 `=> Eq (T0 s0) (ffapp S0 f0 s0) (T1 s1) (ffapp S1 f1 s1)
  -- ElF-Rel S0 S1 (\ s0 s1 -> D s0 s1 .Aye)
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
-}


Dec : U Props -> Set
Dec P = El (P `=> `0) + El P

TabRel : (S0 : UF)(T0 : ElF S0 -> U Data)
         (S1 : UF)(T1 : ElF S1 -> U Data)
         -> (R : (s0 : ElF S0) -> El (T0 s0) -> (s1 : ElF S1) -> El (T1 s1) -> U Props)
         -> (f0 : S0 #> (T0 - El)) -> (f1 : S1 #> (T1 - El)) -> U Props
TabRel S0 T0  S1 T1 R f0 f1 = S0 `#>> \ s0 -> S1 `#>> \ s1 -> EqF S0 s0 S1 s1 `=> R s0 (ffapp S0 f0 s0) s1 (ffapp S1 f1 s1)

-- HERE : finish up this mess. But it'll hopefully improve our life!
-- outstanding Q: what will the off-diagonal look like? A: HORRENDOUS!
TabDec : (S0 : UF)(T0 : ElF S0 -> U Data)(f0 : S0 #> (T0 - El))
         (S1 : UF)(T1 : ElF S1 -> U Data)(f1 : S1 #> (T1 - El))
      -> (R : (s0 : ElF S0) -> El (T0 s0) -> (s1 : ElF S1) -> El (T1 s1) -> U Props)
      -> (DecR : (s0 : ElF S0) (t0 : El (T0 s0)) (s1 : ElF S1) (t1 : El (T1 s1))
             -> Dec (R s0 t0 s1 t1))
      -> Dec (TabRel S0 T0 S1 T1 R f0 f1)
      
TabDec (R0 `>< S0) T0 < f0 > (R1 `>< S1) T1 < f1 > R decR
  with TabDec R0 (\ r0 -> S0 r0 `#>> \ s0 -> T0 (r0 , s0)) f0
          R1 (\ r1 -> S1 r1 `#>> \ s1 -> T1 (r1 , s1)) f1
          (\ r0 g0 r1 g1 ->
            TabRel (S0 r0) ((r0 ,_) - T0) (S1 r1) ((r1 ,_) - T1)
            (\ s0 t0 s1 t1 -> R (r0 , s0) t0 (r1 , s1) t1)
            g0 g1)
          (\ r0 g0 r1 g1 -> TabDec (S0 r0) ((r0 ,_) - T0) g0 (S1 r1) ((r1 ,_) - T1) g1
            (\ s0 t0 s1 t1 -> R (r0 , s0) t0 (r1 , s1) t1)
            (\ s0 t0 s1 t1 -> decR (r0 , s0) t0 (r1 , s1) t1))
... | b , z = {!!} {-
... | `0 , n = `0 , \ f -> n (fflam R0 \ r0 -> fflam R1 \ r1 -> \ rq ->
                          fflam (S0 r0) \ s0 -> fflam (S1 r1) \ s1 -> \ sq ->
                            ffapp (R1 `>< S1) (ffapp (R0 `>< S0) f (r0 , s0)) (r1 , s1) (rq , sq) )
... | `1 , y = `1 , fflam (R0 `>< S0) \ (r0 , s0) -> fflam (R1 `>< S1) \ (r1 , s1) (rq , sq) ->
                 ffapp (S1 r1) (ffapp (S0 r0) (ffapp R1 (ffapp R0 y r0) r1 rq) s0) s1 sq -}
TabDec `0 T0 < f0 > (S1 `>< T) T1 < f1 > R decR = {!!}
TabDec `0 T0 < f0 > `0 T1 < f1 > R decR = {!!}
TabDec `0 T0 < f0 > `1 T1 < f1 > R decR = {!!}
TabDec `0 T0 < f0 > (`E x) T1 < f1 > R decR = {!!}
TabDec `1 T0 < f0 > (R1 `>< S1) T1 < f1 > R decR = `1 , {!!}
TabDec `1 T0 < f0 > `0 T1 < f1 > R decR = {!!}
TabDec `1 T0 < f0 > `1 T1 < f1 > R decR = {!!}
TabDec `1 T0 < f0 > (`E x) T1 < f1 > R decR = {!!}
TabDec (`E x) T0 < f0 > (S1 `>< T) T1 < f1 > R decR = {!!}
TabDec (`E x) T0 < f0 > `0 T1 < f1 > R decR = {!!}
TabDec (`E x) T0 < f0 > `1 T1 < f1 > R decR = {!!}
TabDec (`E x) T0 < f0 > (`E x₁) T1 < f1 > R decR = {!!}

TabDec (_ `>< _) T0 < f0 > `0 T1 < f1 > R decR = {!!}
TabDec (_ `>< _) T0 < f0 > `1 T1 < f1 > R decR = {!!}
TabDec (_ `>< _) T0 < f0 > (`E x) T1 < f1 > R decR = {!!}

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
  TabDec S0 T0 f0 S1 T1 f1 (\ s0 t0 s1 t1 -> Eq (T0 s0) t0 (T1 s1) t1) \ s0 t0 s1 t1 ->
    EqDec (T0 s0) t0 (T1 s1) t1 .decide

EqDec (`F S) s (`F T) t .decide = EqFDec S s T t .decide

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
  = muEq? i0 (muRec (El Ix0) (Sh0 - El) Pos0 posix0 t0) i1 (muRec (El Ix1) (Sh1 - El) Pos1 posix1 t1) where
  muEq? : (i0 : El Ix0) {t0 : El (`Mu Ix0 Sh0 Pos0 posix0 i0)}
          (r0 : MuRec (El Ix0) (Sh0 - El) Pos0 posix0 t0)
          (i1 : El Ix1) {t1 : El (`Mu Ix1 Sh1 Pos1 posix1 i1)}
          (r1 : MuRec (El Ix1) (Sh1 - El) Pos1 posix1 t1)
       ->
        el UPROPS
        (EqDec (`Mu Ix0 Sh0 Pos0 posix0 i0) t0 (`Mu Ix1 Sh1 Pos1 posix1 i1)
         t1 .Naw)
        +
        el UPROPS
        (EqDec (`Mu Ix0 Sh0 Pos0 posix0 i0) t0 (`Mu Ix1 Sh1 Pos1 posix1 i1)
         t1 .Aye)
  muEq? i0 (con s0 k0) i1 (con s1 k1) with EqDec (Sh0 i0) s0 (Sh1 i1) s1 .decide
  ... | `0 , q = `0 , fst - q
  ... | `1 , q = {!!}
  {-
  = poStkEq? (poNil i0) t0 (poNil i1) t1 where
  {- Seems like what we want, but we generalize it (below)
     and make more of it transparently (to Agda) first-order while
     at it.

  -- HERE: refactor using MuRec

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
  -}  
EqDec (`Prf _) _ (`Prf _) _ .decide = `1 , _

-- noises off
EqDec (_ `>< _) _ `1 _ .decide = `1 , _
EqDec (_ `>< _) _ (_ `#>> _) _ .decide = `1 , _
EqDec (_ `>< _) _ (`F _) _ .decide = `1 , _
EqDec (_ `>< _) _ (`List _) _ .decide = `1 , _
EqDec (_ `>< _) _ (`Mu _ _ _ _ _) _ .decide = `1 , _
EqDec (_ `>< _) _ (`Prf _) _ .decide = `1 , _
EqDec `1 _ (_ `>< _) _ .decide = `1 , _
EqDec `1 _ (_ `#>> _) _ .decide = `1 , _
EqDec `1 _ (`F _) _ .decide = `1 , _
EqDec `1 _ (`List _) _ .decide = `1 , _
EqDec `1 _ (`Mu _ _ _ _ _) _ .decide = `1 , _
EqDec `1 _ (`Prf _) _ .decide = `1 , _
EqDec (_ `#>> _) _ (_ `>< _) _ .decide = `1 , _
EqDec (_ `#>> _) _ `1 _ .decide = `1 , _
EqDec (_ `#>> _) _ (`F _) _ .decide = `1 , _
EqDec (_ `#>> _) _ (`List _) _ .decide = `1 , _
EqDec (_ `#>> _) _ (`Mu _ _ _ _ _) _ .decide = `1 , _
EqDec (_ `#>> _) _ (`Prf _) _ .decide = `1 , _
EqDec (`F _) _ (_ `>< _) _ .decide = `1 , _
EqDec (`F _) _ `1 _ .decide = `1 , _
EqDec (`F _) _ (_ `#>> _) _ .decide = `1 , _
EqDec (`F _) _ (`List _) _ .decide = `1 , _
EqDec (`F _) _ (`Mu _ _ _ _ _₁) _ .decide = `1 , _
EqDec (`F _) _ (`Prf _) _ .decide = `1 , _
EqDec (`List _) _ (_ `>< _) _ .decide = `1 , _
EqDec (`List _) _ `1 _ .decide = `1 , _
EqDec (`List _) _ (_ `#>> _) _ .decide = `1 , _
EqDec (`List _) _ (`F _) _ .decide = `1 , _
EqDec (`List _) _ (`Mu _ _ _ _ _) _ .decide = `1 , _
EqDec (`List _) _ (`Prf _) _ .decide = `1 , _
EqDec (`Mu _ _ _ _ _) _ (_ `>< _) _ .decide = `1 , _
EqDec (`Mu _ _ _ _ _) _ `1 _ .decide = `1 , _
EqDec (`Mu _ _ _ _ _) _ (_ `#>> _) _ .decide = `1 , _
EqDec (`Mu _ _ _ _ _) _ (`F _) _ .decide = `1 , _
EqDec (`Mu _ _ _ _ _) _ (`List _) _ .decide = `1 , _
EqDec (`Mu _ _ _ _ _) _ (`Prf _) _ .decide = `1 , _
EqDec (`Prf _) _ (_ `>< _) _ .decide = `1 , _
EqDec (`Prf _) _ `1 _ .decide = `1 , _
EqDec (`Prf _) _ (_ `#>> _) _ .decide = `1 , _
EqDec (`Prf _) _ (`F _) _ .decide = `1 , _
EqDec (`Prf _) _ (`List _) _ .decide = `1 , _
EqDec (`Prf _) _ (`Mu _ _ _ _ _) _ .decide = `1 , _

EqDec T0 t0 T1 t1 .exclude naw aye = naw aye

-- End gazillion
-------------------------------------------------------------------------------

{-
We encounter an amusing situation when function types have unequal domains.
It becomes rather too easy to serve them up "equal inputs".
-}

foo : El {Data} (`E ("fred" ,- []) `#>> \ _ -> `F (`E ("naw" ,- "aye" ,- [])))
foo = fflam (`E ("fred" ,- [])) \ _ -> $ "naw"

bar : El {Data} (`E ("jim" ,- "sheila" ,- []) `#>> \ _ -> `F (`E ("naw" ,- "aye" ,- [])))
bar = fflam (`E ("jim" ,- "sheila" ,- [])) \ _ -> $ "aye"

baz : El {Data} (`E ("jim" ,- "sheila" ,- []) `#>> \ _ -> `F (`E ("naw" ,- "aye" ,- [])))
baz = fflam (`E ("jim" ,- "sheila" ,- [])) \ _ -> $ "naw"

claim : El (Eq {Data} {Data} (`E ("fred" ,- []) `#>> \ _ -> `F (`E ("naw" ,- "aye" ,- []))) foo
               (`E ("jim" ,- "sheila" ,- []) `#>> \ _ -> `F (`E ("naw" ,- "aye" ,- []))) bar
            `=> `0)
claim bad = ffapp (`E ("jim" ,- "sheila" ,- [])) (ffapp (`E ("fred" ,- [])) bad ($ "fred")) ($ "jim") <> 

haha : El (Eq {Data} {Data} (`E ("fred" ,- []) `#>> \ _ -> `F (`E ("naw" ,- "aye" ,- []))) foo
               (`E ("jim" ,- "sheila" ,- []) `#>> \ _ -> `F (`E ("naw" ,- "aye" ,- []))) baz
           )
haha = fflam (`E ("fred" ,- [])) \ {(_ , ze) -> fflam (`E ("jim" ,- "sheila" ,- []))
  \ { (_ , ze) -> _ ; (_ , su ze) -> _}}

{-  -- HERE: use this instead?
Eq (S0 `#>> T0) f0 (S1 `#>> T1) f1 =
  S0 =F= S1 `/\
  S0 `#>> \ s0 -> S1 `#>> \ s1 -> EqF S0 s0 S1 s1 `=> Eq (T0 s0) (ffapp S0 f0 s0) (T1 s1) (ffapp S1 f1 s1)
-}
