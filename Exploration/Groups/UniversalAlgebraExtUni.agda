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

 module SELECTION (R : Sort -> U) where
  -- selection as a relation
  _<?_]_ : {as bs : List Sort}(xs : All (R - El) as)(th : as <= bs)(ys : All (R - El) bs)
     -> P
  xs       <? a ^- th ] (y , ys) =                   xs <? th ] ys
  (x , xs) <? a ,- th ] (y , ys) = Oq (R a) x y `/\ (xs <? th ] ys)
  <>       <? []      ] <>       = `One

  -- select selects
  select-selects :  {as bs : List Sort}(th : as <= bs)(ys : All (R - El) bs)
    -> Pr (select th ys <? th ] ys)
  select-selects (a ^- th) (y , ys) = select-selects th ys
  select-selects (a ,- th) (y , ys) = refl (R a) y , select-selects th ys
  select-selects []        <>       = <>

  riffle-thins : {as bs cs : List Sort}{th : as <= bs}{ph : cs <= bs}
    (xs : All (R - El) as)(p : th /#\ ph)(ys : All (R - El) cs)
    -> Pr ((xs <? th ] (xs /< p >\ ys)) `/\ (ys <? ph ] (xs /< p >\ ys)))
  riffle-thins xs (a ^,- p) (y , ys) =
    let s , t = riffle-thins xs p ys in s , (refl (R a) y , t)
  riffle-thins (x , xs) (a ,^- p) ys =
    let s , t = riffle-thins xs p ys in (refl (R a) x , s) , t
  riffle-thins <> [] <>              = <> , <>

  -- general fact about thinnings
  project-select : {r : Sort} {ss ts : List Sort} {i : r -in ss}{j : r -in ts}{th : ss <= ts}
    -> [ i -< th ]= j -> (ys : All (R - El) ss)(xs : All (R - El) ts)
    -> Pr ((ys <? th ] xs)
       `=> Oq (R r) (project xs j) (project ys i))
  project-select (_ ^- v) xs (y , ys) sel = project-select v xs ys sel
  project-select (_ ^,- v) (x , xs) (y , ys) (_ , sel) = project-select v xs ys sel
  project-select (a ,- _) (_ , _) (_ , _) (q , _) = EQPRF.sym (R a) q

 module _ (R : Sort -> U) where

  -- and now back to our regularly scheduled program
  open Signature Sort

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

     -- TODO: We're going to want some kit that gives us the equivalent of 0 !
     -- but gets fed a model and produces it.

  module _ {wee big : Sig}(ext : wee <Sig= big)
    (Crr : Sort -> U)(wops : Operations Crr wee)(bops : Operations Crr big)
    (sel : (t : Sort) -> let open SELECTION ([ Crr ]-_>> t) in
           Pr (wops t <? ext t ] bops t))
    (V : List Sort)
    (ga : All (Crr - El) V)
    where

    evalEmbed : {t : Sort}(e : FreeOprModel wee V t)
      -> Pr (Oq (Crr t)
          (eval Crr big V bops ga (embed ext e))
          (eval Crr wee V wops ga e))
    evalsEmbeds : {ss : List Sort}(es : All (FreeOprModel wee V) ss)
      -> Pr (Oq (UAll Crr ss) (evals Crr big V bops ga (embeds ext es))
                             (evals Crr wee V wops ga es))

    evalEmbed {t} (Signature.opr c es) =
      let open SELECTION ([ Crr ]-_>> t) in
      project-select (snd (tri c (ext t))) (wops t) (bops t) (sel t)
        (evals Crr big V bops ga (embeds ext es))
        (evals Crr wee V wops ga es) (evalsEmbeds es)
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
      eE = evalEmbed (ext - snd) (Carrier m)
             (\ t -> select (extIsBigger ext t) (operations m t))
             (operations m)
             (\ t -> let open SELECTION ([ Carrier m ]-_>> t) in
                  select-selects (snd (ext t)) (operations m t))
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
             < bleu (eE _ vs oql) ]==
           (eval (Carrier m) (ext - fst) a (operations m) vs (embed (ext - snd) oql))
             ==[ bleu (mq vs) >
           (eval (Carrier m) (ext - fst) a (operations m) vs (embed (ext - snd) oqr))
             ==[ bleu (eE _ vs oqr) >
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
             eE = evalEmbed (ext - snd) (Carrier umod) (operations umod) combined-ops
                    (\ t -> let open SELECTION ([ Carrier umod ]-_>> t) in
                      fst (riffle-thins (operations umod t) (extPart ext t) (extra-ops t)))

             help : (t : Sort) (EqEs : List (List Sort)) (EqQs : Eqns sig EqEs t)
                    -> Equations (umod .Carrier) thy (umod .operations) t EqEs EqQs
                    -> Equations (Carrier umod) extTheory combined-ops t EqEs
                       (mapAll (embed (extIsBigger ext) >><< embed (extIsBigger ext)) EqQs)
             help t [] <> <> = <>
             help t (EqE ,- EqEs) ((eql , eqr) , EqQs) (eqn , eqns) =
               (\ vs -> let open EQPRF (Carrier umod t) in
                vert ((
                eval (Carrier umod) (extBig ext) EqE combined-ops vs (embed (extIsBigger ext) eql)
                  ==[ bleu (eE _ vs eql) >
                eval (Carrier umod) sig EqE (operations umod) vs eql
                  ==[ bleu (eqn vs) >
                eval (Carrier umod) sig EqE (operations umod) vs eqr
                  < bleu (eE _ vs eqr) ]==
                eval (Carrier umod) (extBig ext) EqE combined-ops vs (embed (extIsBigger ext) eqr)
                  [==])))
               , help t EqEs EqQs eqns

        -- now, the model of the extended theory
        uExtended : UModel extTheory
        Carrier uExtended = Carrier umod
        operations uExtended = combined-ops
        equations uExtended = combined-eqs

-- TODO? We're expecting coherence requirements to arise, i.e. if you extend Semigroup to Monoid,
-- then get the inner Semigroup, you expect to get something very-equivalent to the orignal Semigroup.
