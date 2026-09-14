module GhastlyLaws where

open import Basics
open import UF
open import Fontainer

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
    ~[ laqF _ _ (\ p -> mapIdR aa q _ _) >
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
    ~[ laqF _ _ (\ p -> mapExtR q (k $F p) (f p) (k $F p) (g p) r~) >
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
  ((s ,_) - <_>) $~ {!!} -- extF _ _ \ p -> {!mapCoR {rs = rs} {st = st} q (k $F p) (f p)!}

{-(
  (\\F \ p -> mapr st ((\\F \ p -> mapr rs (k $F p) (f p)) $F p) (g p))
    ~[ extF _ _ (\ p -> mapExtR (\ _ -> r~) _ _ _ _
                          (betaF (\ p -> mapr rs (k $F p) (f p)) p)) >
  (\\F \ p -> mapr st (mapr rs (k $F p) (f p)) _)
    ~[ extF _ _ (\ p -> mapCoR q (k $F p) (f p)
        (subst _ _ (betaF (\ p -> mapr rs (k $F p) (f p)) p) Rec (g p))) >
  (\\F \ p -> mapr rt (k $F p) (f p))
    [QED])-}


mapCoR' : forall {C R S T}
  {rs : R -> S}{st : S -> T}{rt : R -> T}
  (q : (r : R) -> st (rs r) ~ rt r)
  (rc : C ^* R)(rcr : Rec rc)
  (sc : C ^* S)(scr : Rec sc)
  ->
  sc ~ (mapr rs rc rcr)
  ->
  mapr st (mapr rs rc rcr) {!!} ~ mapr rt rc rcr
mapCoR' q rc rcr sc scr scq = {!!}

mapCo : forall {C R S T}
  {rs : R -> S}{st : S -> T}{rt : R -> T}
  (q : (r : R) -> st (rs r) ~ rt r)
  (rc : C ^* R)
  ->
  map st (map rs rc) ~ map rt rc
mapCo q rc = mapCoR q rc (rec rc) (rec (mapr _ rc (rec rc)))

