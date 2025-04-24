module UniversalAlgebraExtUni where

open import Basics
open import UniversalAlgebra
open import ExtUni
open import Reasoning
open import Thinnings

module _ {Sort : Set} where

 UAll : (Sort -> U) -> List Sort -> U
 UAll R [] = `One
 UAll R (s ,- ss) = R s `* UAll R ss

 [_]-_>>_ : (Sort -> U) -> List Sort -> Sort -> U
 [ R ]- ss >> t = UAll R ss `> R t

 module _ (R : Sort -> U) where
  -- general fact about thinnings
  project-select : {r : Sort} {ss ts : List Sort} {i : r -in ss}{j : r -in ts}{th : ss <= ts}
    -> [ i -< th ]= j -> (xs : All (R - El) ts)
    -> Pr (Oq (R r) (project xs j) (project (select th xs) i))
  project-select (a ^- v)  (x , xs) = project-select v xs
  project-select (a ^,- v) (x , xs) = project-select v xs
  project-select (_ ,- v)  (x , xs) = refl (R _) x

  -- and now back to our regularly scheduled program
  open Signature Sort

  -- HERE; THOUGHT REQUIRED, THEREFORE ALSO FRESH HORSES
  -- Our uni. alg. setup is not internal to U.
  -- Our models have carriers in U.
  -- We are struggling with the interface between external All and this:

 -- We may also have a problem *stating* functorialty of *external* All
 -- with respect to selection.

 -- How are we going to Jagger/Richards our way out of this one?
 -- Do we move operations, etc into U?

  module _ (sig : Sig) where
    -- Operations (i.e. Model) for raw Signature
    Operations : Set
    Operations = (t : Sort) -> All (\ ss -> El ([ R ]- ss >> t)) (sig t)

    _-op_ : Operations -> forall {ss t} -> ss -in sig t -> El ([ R ]- ss >> t)
    ops -op o = project (ops _) o

    module _ (V : List Sort) where
      eval : Operations
        -> All (R - El) V
        -> [! FreeOprModel sig V -:> R - El !]
      evals : Operations
        -> All (R - El) V
        -> [! All (FreeOprModel sig V) -:> UAll R - El !]
      eval ops ga (opr {ss} o ms) = (ops -op o) (evals ops ga ms)
      eval ops ga (var v) = project ga v
      evals ops ga {[]} <> = <>
      evals ops ga {i ,- is} (t , ts) = eval ops ga t , evals ops ga ts

  module _ {sig : Sig}(thy : Theory sig) where
  
    Equations : (ops : Operations sig)(t : Sort)
                (ES : List (List Sort))(QS : Eqns sig ES t) -> Set
    Equations ops t ES QS =
      Alll -- maybe we'll need a UAll here, but let's see?
        (\ ga -> /\ \ l r -> [:( \ ro ->
         let ev = eval sig ga ops ro in
         Pr (Oq (R t) (ev l) (ev r)) ):])
        ES QS

module _ {Sort : Set} where
  open Signature Sort

  -- need 'internal' map
  mapUAll : (ss : List Sort) (S T : Sort -> U) ->  [! (S - El) -:> (T - El) !] -> El (UAll S ss `> UAll T ss)
  mapUAll []        S T f <>       = <>
  mapUAll (s ,- ss) S T f (v , vs) = (f v) , (mapUAll ss S T f vs)
  
  module _ {sig : Sig}(thy : Theory sig) where
    record UModel : Set where
      open Theory thy

      -- mnemonic: 'q' for 'equation'
      field
        Carrier : Sort -> U
        operations : Operations Carrier sig
        equations : (t : Sort) -> Equations Carrier thy operations t (EqnSig t) (eqns t)

    record _=UModel=>_ (S : UModel)(T : UModel) : Set where
      open UModel
      field
        carrierFun : [! (Carrier S - El) -:> (Carrier T - El) !]
        preservesOprs : (t : Sort) ->
          All
          (/\ \ ss -> /\ \ f g ->
          Pr (UAll (Carrier S) ss `-> \ vs ->
              Oq (Carrier T t) (carrierFun (f vs)) (g (mapUAll ss (Carrier S) (Carrier T) carrierFun vs))))
          -- in principle, this zAll should go away, with Alll above
          (zAll (sig t) (pureAll _,_ <*All*> operations S t <*All*> operations T t))


  module _ {wee big : Sig}(ext : wee <Sig= big) {V : List Sort}
    (Crr : Sort -> U)(ops : Operations Crr big) (ga : All (Crr - El) V)
    where

    evalEmbed : {t : Sort}(e : FreeOprModel wee V t)
      -> Pr (Oq (Crr t)
          (eval Crr big V ops ga (embed ext e))
          (eval Crr wee V (\ s -> select (ext s) (ops s)) ga e))
    evalsEmbeds : {ss : List Sort}(es : All (FreeOprModel wee V) ss)
      -> Pr (Oq (UAll Crr ss) (evals Crr big V ops ga (embeds ext es))
                             (evals Crr wee V (\ s -> select (ext s) (ops s)) ga es))

    evalEmbed {t} (Signature.opr c es) = project-select ([ Crr ]-_>> t) (snd (tri c (ext t))) (ops t)
      (evals Crr big V ops ga (embeds ext es))
      (evals Crr wee V (λ s → select (ext s) (ops s)) ga es) (evalsEmbeds es)
    evalEmbed {t} (Signature.var v) = refl (Crr t) _

    evalsEmbeds {[]}       <>      = <>
    evalsEmbeds {s ,- ss} (x , xs) = (evalEmbed {s} x) , (evalsEmbeds {ss} xs)


  module _ {sig : Sig}{thy : Theory sig}{ext : SigExtension sig}
           (thyExt : TheoryExtension thy ext)
           where
    open Theory
    open TheoryExtension thyExt
    open UModel

    -- This is essentially a Family of 'UModel thy'.
    UForget : UModel extTheory -> UModel thy
    Carrier (UForget m) = Carrier m
    operations (UForget m) t = select (extIsBigger ext t) (operations m t)
    equations (UForget m) t =
      help {EqnSig thy t} {fst (EqnSigExt t)}
           (snd (EqnSigExt t)) (eqns thy t) (eqnsExt t) (equations m t)
      where
      help : forall {wee big} (th : wee <= big) -> let (comp , opth) , apart = th -not in
             (oqs : Eqns sig wee t)(nqs : Eqns (ext - fst) comp t)
         ->  Equations (Carrier m) extTheory (operations m) t big
               (mapAll (embed (ext - snd) >><< embed (ext - snd)) oqs /< apart >\ nqs) 
         ->  Equations (Carrier m) thy (\ t -> select (snd (ext t)) (operations m t)) t wee oqs
      help (a ^- th) oqs (nq , nqs) (mq , mqs) = help th oqs nqs mqs
      help (a ,- th) ((oql , oqr) , oqs) nqs (mq , mqs)
        = (\ vs -> let open EQPRF (Carrier m t) in
           vert (
           (eval (Carrier m) sig a (\ t -> select (snd (ext t)) (operations m t)) vs oql)
             < bleu (evalEmbed (ext - snd) (Carrier m) (operations m) vs oql) ]==
           (eval (Carrier m) (ext - fst) a (operations m) vs (embed (ext - snd) oql))
             ==[ bleu (mq vs) >
           (eval (Carrier m) (ext - fst) a (operations m) vs (embed (ext - snd) oqr))
             ==[ bleu (evalEmbed (ext - snd) (Carrier m) (operations m) vs oqr) >
           (eval (Carrier m) sig a (\ t -> select (snd (ext t)) (operations m t)) vs oqr) [==]))
        , help th oqs nqs mqs
      help [] <> <> <> = <>


    module _ (umod : UModel thy) where
      -- What is the data of a UModel extension?
      record UExtend : Set where
        field
          extra-ops : Operations (Carrier umod) (extCompSig ext)

        combined-ops : Operations (Carrier umod) (extBig ext)
        combined-ops s = operations umod s /< extPart ext s >\ extra-ops s

        field
          extra-eqs : (t : Sort) -> Equations (Carrier umod) extTheory combined-ops t
                      (extCompSig EqnSigExt t)
                      (eqnsExt t)

        combined-eqs : (t : Sort) -> Equations (Carrier umod) extTheory combined-ops t
                      (EqnSig extTheory t) (eqns extTheory t)
        combined-eqs t = help t (EqnSig thy t) (eqns thy t) (equations umod t)
                         /<< extPart EqnSigExt t >>\
                         extra-eqs t
           where
             help : (t : Sort) (EqEs : List (List Sort)) (EqQs : Eqns sig EqEs t)
                    -> Equations (umod .Carrier) thy (umod .operations) t EqEs EqQs
                    -> Equations (Carrier umod) extTheory combined-ops t EqEs
                       (mapAll (embed (extIsBigger ext) >><< embed (extIsBigger ext)) EqQs)
             help t [] <> <> = <>
             help t (EqE ,- EqEs) ((eql , eqr) , EqQs) (eqn , eqns) =
               (\ vs -> let open EQPRF (Carrier umod t) in
                vert ((
                eval (Carrier umod) (extBig ext) EqE combined-ops vs (embed (extIsBigger ext) eql)
                  -- HERE: we should use a generalized 'evalEmbed' here that abstracts over the
                  -- exact means of selection.
                  ==[ {!!} >
                eval (Carrier umod) sig EqE (operations umod) vs eql
                  ==[ bleu (eqn vs) >
                eval (Carrier umod) sig EqE (operations umod) vs eqr
                  ==[ {!!} >
                eval (Carrier umod) (extBig ext) EqE combined-ops vs (embed (extIsBigger ext) eqr)
                  [==])))
               , help t EqEs EqQs eqns
