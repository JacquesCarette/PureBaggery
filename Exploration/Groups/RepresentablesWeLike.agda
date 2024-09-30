{-# OPTIONS --allow-unsolved-metas #-}
module RepresentablesWeLike where

open import Basics
open import Quotient
open import ExtUni
open import Reasoning
open import Actions
open import Iso
open import GroupsWeLike
open import ActionsWeLike
open import Representables

-- Some simple representables

AsFunFrom : U -> Representable
AsFunFrom S = record { Positions = S ; Grp = Trivial ; Act = IdentityAct Trivial S }

-- Jumble by *all* the Automorphisms of a position set
JumbleR : U -> Representable
JumbleR P = record { Positions = P ; Grp = Automorphism P ; Act = AutAct P }

Jumble : U -> U -> U
Jumble P X = `UQuot (FObjUQuot X) where
  open REPRESENTABLE (JumbleR P)

module _ (X : U){P Q : U}(pq : P <==> Q) where
  open EQPRF X

  isoPmapJumble : El (Jumble P X `> Jumble Q X)
  isoPmapJumble [f] = elElim (Jumble P X) [f] (\ _ -> Jumble Q X)
    ( (\ f -> `[ bwd pq - f ])
    , \ h k hk -> homogTac (Jumble Q X) `[ bwd pq - h ] `[ bwd pq - k ]
      (mapHide (\ (pr , hkP) -> osi (via (iso' {P}{P} pr) pq) ,
        homogTac (Q `> X) _ _ \ x -> vert (
            h (bwd pq (fwd pq (bwd (iso' {P}{P} pr) (bwd pq x))))
              ==[ congB P h (fwd-bwd pq _) >
            h (bwd (iso' {P}{P} pr) (bwd pq x))
              ==[ bleu (hkP (bwd pq x) (bwd pq x) (refl P _)) >
            k (bwd pq x)
              [==])
        ) hk)
    )

-- can't unify this with above module as we need to be able to specify which
-- iso to use (i.e. forward or backward) below
module _ (X : U){P Q : U}(pq : P <==> Q) where
  open EQPRF X

  -- an isomorphism on positions induces one on jumbles
  isoPisoJumbleP : Jumble P X <==> Jumble Q X
  fwd isoPisoJumbleP = isoPmapJumble X pq
  bwd isoPisoJumbleP = isoPmapJumble X (invIso' pq)
  fwd-bwd isoPisoJumbleP [f] = elElim (Jumble P X) [f]
    (\ [f] -> `Pr (Oq (Jumble P X) (bwd isoPisoJumbleP (fwd isoPisoJumbleP [f])) [f]))
    ( (\ f -> homogTac (Jumble P X) (bwd isoPisoJumbleP (fwd isoPisoJumbleP `[ f ])) `[ f ]
        (hide (idIso P , homogTac (P `> X) ((fwd pq - bwd pq) - f) f
          \ p -> vert (congB P f (fwd-bwd pq p)))))
    , _
    )
  bwd-fwd isoPisoJumbleP [f] = elElim (Jumble Q X) [f]
    (\ [f] -> `Pr (Oq (Jumble Q X) (fwd isoPisoJumbleP (bwd isoPisoJumbleP [f])) [f]))
    ( (\ f -> homogTac (Jumble Q X) (fwd isoPisoJumbleP (bwd isoPisoJumbleP `[ f ])) `[ f ]
        (hide (idIso Q , homogTac (Q `> X) ((bwd pq - fwd pq) - f) f
          \ q -> vert (congB Q f (bwd-fwd pq q)))))
    , _
    )
