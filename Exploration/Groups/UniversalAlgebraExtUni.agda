module UniversalAlgebraExtUni where

open import Basics
open import UniversalAlgebra
open import ExtUni
open import Reasoning

module _ {Sort : Set} where
  open Signature Sort

  -- HERE; THOUGHT REQUIRED, THEREFORE ALSO FRESH HORSES
  -- Our uni. alg. setup is not internal to U.
  -- Our models have carriers in U.
  -- We are struggling with the interface between external All and this:

  UAll : (Sort -> U) -> List Sort -> U
  UAll R [] = `One
  UAll R (s ,- ss) = R s `* UAll R ss

  -- obfuscated identity function!
  uAll : (R : Sort -> U)(ss : List Sort) -> All (R - El) ss -> El (UAll R ss)
  uAll R [] <> = <>
  uAll R (s ,- ss) (r , rs) = r , uAll R ss rs

  uop : (R : Sort -> U)(ss : List Sort)(t : Sort)(f : [ R - El ]- ss >> t)
        -> El (UAll R ss `> R t)
  uop R [] t f rs = f
  uop R (s ,- ss) t f (r , rs) = uop R ss t (f r) rs

  uopLemma : (R : Sort -> U)(ss : List Sort)(t : Sort)(f : [ R - El ]- ss >> t)
    (rs : All (R - El) ss)
    -> Pr (Oq (R t) (sortApply (R - El) ss (El (R t)) f rs) (uop R ss t f (uAll R ss rs)))
  uopLemma R [] t f rs = refl (R t) f
  uopLemma R (s ,- ss) t f (r , rs) = uopLemma R ss t (f r) rs

  -- We may also have a problem *stating* functorialty of *external* All
  -- with respect to selection.

  -- How are we going to Jagger/Richards our way out of this one?
  -- Do we move operations, etc into U?

  module _ {sig : Sig}(thy : Theory sig) where
  
    Equations : (Ca : Sort -> U)(ops : Operations sig (Ca - El))(t : Sort)(ES : List (List Sort))(QS : Eqns sig ES t) -> Set
    Equations Ca ops t ES QS =
      All
        (/\ \ ga -> /\ \ l r -> [:( \ ro ->
         let ev = eval sig ga ops ro in
         Pr (Oq (Ca t) (ev l) (ev r)) ):])
        (zAll ES QS)

    record UModel : Set where
      open Theory thy


      -- mnemonic: 'q' for 'equation'
      field
        Carrier : Sort -> U
        operations : Operations sig (Carrier - El)
        equations : (t : Sort) -> Equations Carrier operations t (EqnSig t) (eqns t)

    record _=UModel=>_ (S : UModel)(T : UModel) : Set where
      open UModel
      field
        carrierFun : [! (Carrier S - El) -:> (Carrier T - El) !]
        preservesOprs : (t : Sort) -> 
          All
          (/\ \ ss -> /\ \ f g -> (vs : All (Carrier S - El) ss) ->
            Pr (Oq (Carrier T t)
                   (carrierFun (sortApply _ ss _ f vs))
                   (sortApply _ ss _ g (mapAll carrierFun vs))))
          (zAll (sig t) (pureAll _,_ <*All*> operations S t <*All*> operations T t))

  module _ {wee big : Sig}(ext : wee <Sig= big) {V : List Sort}
    (Crr : Sort -> U)(ops : Operations big (Crr - El))(ga : All (Crr - El) V)
    where

    evalEmbed : {t : Sort}(e : FreeOprModel wee V t)
      -> Pr (Oq (Crr t)
          (eval big V ops ga (embed ext e))
          (eval wee V (\ s -> select (ext s) (ops s)) ga e))

{-
    evalsEmbeds : {ss : List Sort}(es : All (FreeOprModel wee V) ss)
      -> Pr (Oq (Crr t)
          (eval big V ops ga (embed ext e))
          (eval wee V (\ s -> select (ext s) (ops s)) ga e)) 
-}

    evalEmbed {t} (Signature.opr c es) = {!!}
    evalEmbed {t} (Signature.var v) = refl (Crr t) _



  module _ {sig : Sig}{thy : Theory sig}{ext : SigExtension sig}
           (thyExt : TheoryExtension thy ext)
           where
    open Theory
    open TheoryExtension thyExt
    open UModel

    UForget : UModel extTheory -> UModel thy
    Carrier (UForget m) = Carrier m
    operations (UForget m) t = select (extIsBigger ext t) (operations m t)
    equations (UForget m) t = help {EqnSig thy t} {fst (EqnSigExt t)} (snd (EqnSigExt t)) (eqns thy t) (eqnsExt t) (equations m t)
      where
      help : forall {wee big} (th : wee <= big) -> let (comp , opth) , apart = th -not in
             (oqs : Eqns sig wee t)(nqs : Eqns (ext - fst) comp t)
         ->  Equations extTheory (Carrier m) (operations m) t big
               (mapAll (embed (ext - snd) >><< embed (ext - snd)) oqs /< apart >\ nqs) 
         ->  Equations thy (Carrier m) (\ t -> select (snd (ext t)) (operations m t)) t wee oqs
      help (a ^- th) oqs (nq , nqs) (mq , mqs) = help th oqs nqs mqs
      help (a ,- th) ((oql , oqr) , oqs) nqs (mq , mqs)
        = (\ vs -> let open EQPRF (Carrier m t) in
           vert (
           (eval sig a (\ t -> select (snd (ext t)) (operations m t)) vs oql)
             < bleu (evalEmbed (ext - snd) (Carrier m) (operations m) vs oql) ]==
           (eval (ext - fst) a (operations m) vs (embed (ext - snd) oql))
             ==[ bleu (mq vs) >
           (eval (ext - fst) a (operations m) vs (embed (ext - snd) oqr))
             ==[ bleu (evalEmbed (ext - snd) (Carrier m) (operations m) vs oqr) >
           (eval sig a (\ t -> select (snd (ext t)) (operations m t)) vs oqr) [==]))
        , help th oqs nqs mqs
                                              -- ^^^^^ HERE
      help [] <> <> <> = <>

