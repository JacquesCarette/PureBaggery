module Perm where

record _><_ (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open _><_
infixr 6 _,_

module _ {X : Set} where
  data _~_ (x : X) : X -> Set where
    r~ : x ~ x

  <_> : (X -> Set) -> Set
  < T > = X >< T

  _*:_ : (X -> Set) -> (X -> Set) -> (X -> Set)
  (S *: T) x = S x >< \ _ -> T x

  infix 5 <_>
  infixr 6 _*:_

data List (X : Set) : Set where
  [] : List X
  _,-_ : X -> List X -> List X

infixr 20 _,-_

module _ {X : Set} where

  infix 10 _<<_>>_

  data _<<_>>_ : List X -> List X -> List X -> Set where
    _,^-_ : forall x {xs zs ys} -> xs << zs >> ys -> x ,- xs << x ,- zs >> ys
    _^,-_ : forall y {xs zs ys} -> xs << zs >> ys -> xs << y ,- zs >> y ,- ys
    []   : [] << [] >> []

  swapPar : forall {xs zs ys} -> xs << zs >> ys -> ys << zs >> xs
  swapPar (x ,^- p) = x ^,- swapPar p
  swapPar (y ^,- p) = y ,^- swapPar p
  swapPar [] = []
  
  rotrPar : forall {xs ys zs as}
      -> <  xs <<_>> ys   *:  _<< as >> zs  >
      -> <  xs << as >>_  *:  ys <<_>> zs   >
  rotrPar (_ , p , (z ^,- q))          = let _ , r , s = rotrPar (_ , p , q) in
    _ , z ^,- r , z ^,- s
  rotrPar (_ , (.y ^,- p) , (y ,^- q)) = let _ , r , s = rotrPar (_ , p , q) in
    _ , y ^,- r , y ,^- s
  rotrPar (_ , (.x ,^- p) , (x ,^- q)) = let _ , r , s = rotrPar (_ , p , q) in
    _ , x ,^- r , s
  rotrPar (_ , [] , []) = _ , [] , []

  allRPar : forall {xs} -> [] << xs >> xs
  allRPar {[]} = []
  allRPar {x ,- xs} = x ^,- allRPar {xs}

  isAllRPar : forall {xs ys} -> [] << xs >> ys -> xs ~ ys
  isAllRPar (y ^,- p) with r~ <- isAllRPar p = r~
  isAllRPar [] = r~

  infix 10 _~~_

  data _~~_ : List X -> List X -> Set where
    _,-_ : forall {x xs ys ys'}
      -> x ,- [] << ys' >> ys
      -> xs ~~ ys
      -> x ,- xs ~~ ys'
    [] : [] ~~ []

  insPerm : forall {x xs xs' ys ys'}
    -> x ,- [] << xs' >> xs
    -> x ,- [] << ys' >> ys
    -> xs ~~ ys
    -> xs' ~~ ys'
  insPerm (_ ,^- x) y p = y ,- help where
    help : _
    help with r~ <- isAllRPar x = p
  insPerm (_ ^,- x) y (z ,- p) = let _ , a , b = rotrPar (_ , z , swapPar y) in
    a ,- insPerm x (swapPar b) p

  symPerm : forall {xs ys} -> xs ~~ ys -> ys ~~ xs
  symPerm (x ,- p) = insPerm x (_ ,^- allRPar) (symPerm p)
  symPerm [] = []

  delPerm : forall {x xs ys'}
         -> <  x ,- []  <<_>> xs  *:  _~~ ys'             >
         -> <             xs ~~_  *:  x ,- [] << ys' >>_  >
  delPerm (_ , (_ ,^- x) , (y ,- p)) with r~ <- isAllRPar x = _ , p , y
  delPerm (_ , (_ ^,- x) , (y ,- p))
    with _ , q , z <- delPerm (_ , x , p)
    with _ , a , b <- rotrPar (_ , z , swapPar y)
    = _ , swapPar b ,- q , a

  transPerm : forall {xs ys zs} -> xs ~~ ys -> ys ~~ zs -> xs ~~ zs
  transPerm (x ,- p) q
    with _ , q' , y <- delPerm (_ , x , q)
    = y ,- transPerm p q'
  transPerm [] [] = []
