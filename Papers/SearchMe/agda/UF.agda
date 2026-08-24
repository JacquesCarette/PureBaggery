module UF where

open import Basics
open import UE

data UF : Set
[_]F : UF -> Set

data UF where
  `[_] : UE -> UF
  _`><_ : (S : UF)(T : [ S ]F -> UF) -> UF

-- skipping _`->_

[ `[ N ] ]F = [ N ]E
[ S `>< T ]F = [ S ]F >< \ s -> [ T s ]F

_~F>_ : (S : UF)(T : [ S ]F -> Set) -> Set
data _-F>_ (S : UF)(T : [ S ]F -> Set) : Set where
  <_> : S ~F> T -> S -F> T
`[ N ] ~F> T = N  -E> T
(R `>< S) ~F> T = R -F> \ r -> S r -F> \ s -> T (r , s)

\\F : {S : UF}{T : [ S ]F -> Set}
   -> ((x : [ S ]F) -> T x)
   -> S -F> T
\\F {`[ N ]} f = < \\E f >
\\F {R `>< S} f = < (\\F \ r -> \\F \ s -> f (r , s)) >

_$F_ : {S : UF}{T : [ S ]F -> Set}
   -> S -F> T
   -> ((x : [ S ]F) -> T x)
_$F_ {`[ N ]} < k > x = k $E x
_$F_ {R `>< S} < k > (r , s) = k $F r $F s

infixl 30 _$F_

betaF : {S : UF}{T : [ S ]F -> Set}
   -> (f : (x : [ S ]F) -> T x)
   -> (x : [ S ]F) -> (\\F f $F x) ~ f x
betaF {`[ ts ]} f x = betaE f x
betaF {R `>< S} f (r , s) = 
  (\\F \ r -> \\F \ s -> f (r , s)) $F r $F s
     ~[ (_$F s) $~ betaF (\ r -> \\F \ s -> f (r , s)) r >
  (\\F \ s -> f (r , s)) $F s
    ~[ betaF (\ s -> f (r , s)) s >
  f (r , s) [QED]

extF : {S : UF}{T : [ S ]F -> Set}
    -> (f g : (x : [ S ]F) -> T x)
    -> ((x : [ S ]F) -> f x ~ g x)
    -> \\F f ~ \\F g
extF {`[ ts ]} f g q = <_> $~ extE f g q
extF {S `>< T} f g q = <_> $~
  extF _ _ \ r -> extF _ _ \ s -> q (r , s)

etaF : {S : UF}{T : [ S ]F -> Set}
    -> (k : S -F> T)
    -> (\\F \ i -> k $F i) ~ k
etaF {`[ ts ]} < k > = <_> $~ etaE k
etaF {R `>< S} < k > = <_> $~ (
  (\\F \ r -> \\F \ s -> k $F r $F s)
    ~[ extF _ _ (\ r -> etaF (k $F r)) >
  \\F (_$F_ k)
    ~[ etaF k >
  k [QED])

poiF : {S : UF}{T : [ S ]F -> Set}
    -> {f g : S -F> T}
    -> (q : (s : [ S ]F) -> f $F s ~ g $F s)
    -> f ~ g
poiF {f = f}{g} q = 
  f < etaF f ]~
  \\F (f $F_) ~[ extF _ _ q >
  \\F (g $F_) ~[ etaF g >
  g [QED]


