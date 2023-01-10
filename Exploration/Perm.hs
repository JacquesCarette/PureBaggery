{-# LANGUAGE TypeFamilies, TypeOperators, DeriveFunctor #-}

module Perm where

import Control.Applicative
import Data.List

class Functor f => Diffable f where
  type D f :: * -> *
  up    :: (x, D f x) -> f x
  down  :: f x -> f (x, D f x)

newtype I x = I {unI :: x}
data (:*:) f g x = f x :&: g x deriving Functor
data (:+:) f g x = Inl (f x) | Inr (g x) deriving Functor

instance Diffable [] where
  type D [] = [] :*: []
  up (y, xs :&: zs) = xs ++ y : zs
  down [] = []
  down (x : xs) = (x, [] :&: xs) : [(y, (x : xs) :&: zs) | (y, xs :&: zs) <- down xs]
  
newtype C x = C {unC :: [x]} deriving (Functor, Show, Eq, Ord)
instance Diffable C where
  type D C = []
  up (x, xs) = C (x : xs)
  down (C xs) = C [(y, zs ++ xs) | (y, xs :&: zs) <- down xs]

newtype P = P {unP :: [C Int]} deriving (Show, Eq)
instance Ord P where
  compare (P xcs) (P ycs) = case compare (length xcs) (length ycs) of
    EQ -> compare xcs ycs
    o  -> o

act :: Int -> P -> Int
act n (P xcs) = case foldr ((<|>) . go) empty xcs of
    Just m -> m
    _ -> n
  where
    go xc = case lookup n (unC (down xc)) of
      Just (m : _) -> Just m
      _ -> Nothing

hi :: [P] -> Int
hi ps = maximum (negate 1 : (ps >>= \ (P xcs) -> xcs >>= unC))

graph :: P -> [Int]
graph p = [act n p | n <- [0 .. hi [p]]]

phrag :: [Int] -> P
phrag g = P (chases (zip [0..] g)) where
  chases xys = case dropWhile (uncurry (==)) xys of
    [] -> []
    ((x, y) : xys) ->
      let (ys, xys') = chase x y xys
      in  C (x : ys) : chases xys'
  chase x y xys = case [(z, ps ++ qs) | ((y', z), ps :&: qs) <- down xys, y == y'] of
    [(z, xys)]
      | z == x -> ([y], xys)
      | otherwise -> case chase x z xys of
          (zs, xys) -> (y : zs, xys)

instance Semigroup P where (<>) = mappend
instance Monoid P where
  mempty = P []
  mappend p q = phrag [act (act n p) q | n <- [0..hi [p,q]]]

inv :: P -> P
inv p = phrag (map snd (sort (zip (graph p) [0..])))

gclose :: [P] -> [P]
gclose ps = let ps' = nub (sort (mempty : map inv ps ++ [p <> q | p <- ps, q <- ps])) in
  if ps == ps' then ps else gclose ps'

gcore :: [P] -> [P]
gcore ps = sort (go ([], gclose [])) where
  gs = gclose ps
  go (qs, qs') = case [q | q <- gs, not (elem q qs')] of
    [] -> qs
    d : _ -> let dqs = d : qs in go (dqs, gclose dqs)