{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module Algebra.Graph.Basic (
    Basic (..), fold, Reflexive, Undirected, PartialOrder, EdgeOrdered
    ) where

import Control.Monad
import Test.QuickCheck

import Algebra.Graph
import Algebra.Graph.AdjacencyMap hiding (transpose)
import Algebra.Graph.Relation
import Algebra.Graph.Util

import Data.Map (Map, (!))
import qualified Data.Map as Map
import qualified Data.List as List

data Basic a = Empty
             | Vertex a
             | Overlay (Basic a) (Basic a)
             | Connect (Basic a) (Basic a)
             deriving (Show, Functor, Foldable, Traversable)

instance Graph (Basic a) where
    type Vertex (Basic a) = a
    empty   = Empty
    vertex  = Vertex
    overlay = Overlay
    connect = Connect

instance Arbitrary a => Arbitrary (Basic a) where
    arbitrary = arbitraryGraph

    shrink Empty         = []
    shrink (Vertex    _) = [Empty]
    shrink (Overlay x y) = [Empty, x, y]
                        ++ [Overlay x' y' | (x', y') <- shrink (x, y) ]
    shrink (Connect x y) = [Empty, x, y, Overlay x y]
                        ++ [Connect x' y' | (x', y') <- shrink (x, y) ]

instance Num a => Num (Basic a) where
    fromInteger = Vertex . fromInteger
    (+)         = Overlay
    (*)         = Connect
    signum      = const Empty
    abs         = id
    negate      = id

instance Ord a => Eq (Basic a) where
    x == y = toAdjacencyMap x == toAdjacencyMap y

toAdjacencyMap :: Ord a => Basic a -> AdjacencyMap a
toAdjacencyMap = fold

instance Applicative Basic where
    pure  = vertex
    (<*>) = ap

instance Monad Basic where
    return = vertex
    (>>=)  = flip foldMapBasic

fold :: (Vertex g ~ a, Graph g) => Basic a -> g
fold = foldMapBasic vertex

foldMapBasic :: (Vertex g ~ b, Graph g) => (a -> g) -> Basic a -> g
foldMapBasic _ Empty         = empty
foldMapBasic f (Vertex  x  ) = f x
foldMapBasic f (Overlay x y) = overlay (foldMapBasic f x) (foldMapBasic f y)
foldMapBasic f (Connect x y) = connect (foldMapBasic f x) (foldMapBasic f y)

newtype Reflexive a = R { fromReflexive :: Basic a }
    deriving (Arbitrary, Functor, Foldable, Num, Show)

instance Ord a => Eq (Reflexive a) where
    x == y = toReflexiveRelation x == toReflexiveRelation y

toReflexiveRelation :: Ord a => Reflexive a -> Relation a
toReflexiveRelation = reflexiveClosure . fold . fromReflexive

newtype Undirected a = U { fromUndirected :: Basic a }
    deriving (Arbitrary, Functor, Foldable, Num, Show)

instance Ord a => Eq (Undirected a) where
    x == y = bidirect x == bidirect y

bidirect :: Undirected a -> Basic a
bidirect (U g) = g `overlay` transpose (fold g)

newtype PartialOrder a = PO { fromPartialOrder :: Basic a }
    deriving (Arbitrary, Functor, Foldable, Num, Show)

instance Ord a => Eq (PartialOrder a) where
    x == y = toTransitiveRelation x == toTransitiveRelation y

toTransitiveRelation :: Ord a => PartialOrder a -> Relation a
toTransitiveRelation = transitiveClosure . fold . fromPartialOrder

-- To be derived automatically using GeneralizedNewtypeDeriving in GHC 8.2
instance Graph (Reflexive a) where
    type Vertex (Reflexive a) = a
    empty       = R empty
    vertex      = R . vertex
    overlay x y = R $ fromReflexive x `overlay` fromReflexive y
    connect x y = R $ fromReflexive x `connect` fromReflexive y

-- To be derived automatically using GeneralizedNewtypeDeriving in GHC 8.2
instance Graph (Undirected a) where
    type Vertex (Undirected a) = a
    empty       = U empty
    vertex      = U . vertex
    overlay x y = U $ fromUndirected x `overlay` fromUndirected y
    connect x y = U $ fromUndirected x `connect` fromUndirected y

-- To be derived automatically using GeneralizedNewtypeDeriving in GHC 8.2
instance Graph (PartialOrder a) where
    type Vertex (PartialOrder a) = a
    empty       = PO empty
    vertex      = PO . vertex
    overlay x y = PO $ fromPartialOrder x `overlay` fromPartialOrder y
    connect x y = PO $ fromPartialOrder x `connect` fromPartialOrder y


------ By LF ------


-- Order is induced by order :: Map. If two values are equal then we compare keys. This function merges 
-- two sorted lists according to order given in order::Map. It requires the lists to be sorted already 
-- according to the order (analogous to merge in mergesort). 
ordered_merge :: (Ord a, Ord b) => Map a b -> [a] -> [a] -> [a] 
ordered_merge _ xs []       = xs 
ordered_merge _ [] xs       = xs 
ordered_merge order (x:xs)(y:ys)= if xo == yo then (x:(ordered_merge order xs ys)) else 
                          if xo < yo  then (x:(ordered_merge order xs (y:ys))) else
                          (y:(ordered_merge order (x:xs) ys))
                          where xo = ((!) order x, x)
                                yo = ((!) order y, y)


-- Sorts a list according to the order given in order::Map.
ordered_sort :: (Ord a, Ord b) => Map a b -> [a] -> [a]
ordered_sort order list = List.sortBy (\a0 a1 -> compare (((!) order a0), a0) (((!) order a1), a1)) list

-- Unions two maps based on their keys. If key is present only in one map, then result will get the 
-- value of this map. If key is present in both maps, then if and only if the value is the same in both maps, we get that,  
-- otherwise, it hrows an error if there are collisions.
union' :: (Ord k, Ord a) => Map k a -> Map k a -> Map k a
union' m0 m1 = Map.unionWith (\a0 a1 -> if a0 == a1 then a0 else error "collision") m0 m1


-- EdgeOrdered is an extension of the Graph type that provides an order on edges. This is achieved by extending 
-- vertices with a label (b type), and ordering incoming vertices according to this label. Ver stores the ordering, and
-- gr keeps a list of incoming edges.
data EdgeOrdered a b = EdgeOrdered { ver :: Map a b, gr :: Map a [a] }
    deriving (Eq, Show)

instance (Ord a, Ord b, Bounded b) => Graph (EdgeOrdered a b) where
    type Vertex (EdgeOrdered a b) = (a, b)
    empty       = EdgeOrdered Map.empty Map.empty
    vertex  x   = EdgeOrdered (Map.singleton (fst x) (snd x)) (Map.singleton (fst x) [])
    overlay x y = EdgeOrdered new_vertices edges
        where new_vertices = union' (ver x) (ver y)
              edges = Map.unionWith (\es0 es1 -> ordered_merge new_vertices es0 es1) (gr x) (gr y)
    connect x y = ov_final
        where ov = overlay x y
              new_vertices = union' (ver x) (ver y)
              ordered_x = ordered_sort new_vertices (Map.keys (ver x))
              new_edges_list = map (\v -> (v, ordered_merge new_vertices ordered_x ((!) (gr y) v))) (Map.keys (ver y))            
              new_edges = Map.fromList new_edges_list
              ov_final = overlay ov (EdgeOrdered new_vertices new_edges)

-- EdgeOrdered graph generator, which generates graphs without collision on vertices. This is achieved by giving the same
-- label to every vertex. In the case that two vertices have the same label, then the order is given by the vertex index. 
instance (Ord a, Ord b, Bounded b, Arbitrary a, Arbitrary b) => Arbitrary (EdgeOrdered a b) where 
    arbitrary = sized graph
                where
                  graph 0 = return empty
                  graph 1 = do
                    x :: (a, b) <- arbitrary
                    return $ vertex (fst x, minBound :: b)
                  graph n = do
                    left <- choose (0, n)
                    oneof [ overlay <$> (graph left) <*> (graph $ n - left)
                          , connect <$> (graph left) <*> (graph $ n - left) ]

