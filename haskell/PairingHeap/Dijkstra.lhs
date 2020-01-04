%include polycode.fmt
%subst keyword a = "\textcolor{BlueViolet}{\textbf{" a "}}"
%format <> = "\hcmb "
%format inv (a) = a "^{-1} "
%format <*> = "\hap "
%format <>< = "\hcmbin "
%format x1 = "x_1"
%format x2 = "x_2"
%format x3 = "x_3"
%format mconcat = "\sum "
%format mempty = "\epsilon "
%format <|> = "\halt "
\begin{code}
{-# LANGUAGE DeriveFunctor, LambdaCase, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, UndecidableInstances, RankNTypes, GeneralizedNewtypeDeriving #-}

module PairingHeap.Dijkstra where

import Data.Semigroup hiding (Sum(..))
import Control.Applicative
import Control.Monad
import Data.Functor.Classes
import Control.Monad.State
import qualified Data.Set as Set
import Data.Set (Set)
import Control.Monad.Except
import Data.List

newtype Sum a = Sum { getSum :: a } deriving (Eq, Ord, Num)

instance Show a => Show (Sum a) where
    showsPrec n = showsPrec n . getSum
    
instance Num a => Semigroup (Sum a) where
    Sum x <> Sum y = Sum (x + y)
    
instance Num a => Monoid (Sum a) where
    mappend = (<>)
    mempty = Sum 0

class (Monoid a, Semigroup a) => Group a where
    inv :: a -> a
    
data Heap a b
    = Leaf
    | Node a b [Heap a b]
    deriving Show
    
instance (Ord a, Group a) => Semigroup (Heap a b) where
    Leaf <> ys = ys
    xs <> Leaf = xs
    Node x xv xs <> Node y yv ys 
      | x <= y    = Node x xv (Node (inv x <> y) yv ys : xs)
      | otherwise = Node y yv (Node (inv y <> x) xv xs : ys)

instance (Ord a, Group a) => Monoid (Heap a b) where
    mempty = Leaf
    mappend = (<>)
    mconcat = mergeHeaps id
    
instance Functor (Heap a) where
    fmap f Leaf = Leaf
    fmap f (Node k x xs) = Node k (f x) (map (fmap f) xs)

(<><) :: Semigroup a => a -> Heap a b -> Heap a b
x <>< Leaf = Leaf
x <>< Node y yv ys = Node (x <> y) yv ys

mergeHeaps :: (Group a, Ord a) => (c -> Heap a b) -> [c] -> Heap a b
mergeHeaps _ [] = Leaf
mergeHeaps f (x : xs) = go x xs
  where
    go x [] = f x
    go x1 (x2 : []) = f x1 <> f x2
    go x1 (x2 : x3 : xs) = (f x1 <> f x2) <> go x3 xs

instance (Group a, Ord a) => Applicative (Heap a) where
    pure x = Node mempty x []
    (<*>) = ap
    
instance (Group a, Ord a) => Monad (Heap a) where
  Leaf >>= _ = Leaf
  Node k x xs >>= f = k <>< (mergeHeaps (>>= f) xs <> f x)
      
instance (Group a, Ord a) => Alternative (Heap a) where
    empty = mempty
    (<|>) = (<>)
instance (Group a, Ord a) => MonadPlus (Heap a) where
\end{code}
%<*monstar>
\begin{code}
class MonadPlus m => MonadStar m where
    star :: (a -> m a) -> a -> m a
    plus :: (a -> m a) -> a -> m a
    star f x = pure x <|> plus f x
    plus f x = star f x >>= f
\end{code} 
%</monstar>
%<*heap-inst>
\begin{code}
instance (Group a, Ord a)
      => MonadStar (Heap a) where
    star f x = Node mempty x (go (f x))
      where
        go Leaf = []
        go (Node k x xs) =
          [Node k x (go (mconcat xs <> f x))]
\end{code}
%</heap-inst>
%<*state-inst>
\begin{code}
instance MonadStar m
      => MonadStar (StateT s m) where
    star f x =
      StateT
        (star (uncurry (runStateT . f)) . (,) x)

\end{code}
%</state-inst>
\begin{code}
popMin :: (Ord a, Group a) => Heap a b -> Maybe (b, Heap a b)
popMin Leaf = Nothing
popMin (Node x xv xs) = Just (xv, x <>< mergeHeaps id xs)

toList :: (Ord a, Group a) => Heap a b -> [b]
toList = unfoldr popMin

prio :: a -> b -> Heap a b
prio k v = Node k v []

fromList :: (Ord a, Group a) => [(a,b)] -> Heap a b
fromList = foldMap (uncurry prio)
\end{code}
%<*graph>
\begin{code}
type Graph a b = b -> [(a,b)]

type GraphT a t b = b -> t (Heap a) b
\end{code}
%</graph>
\begin{code}
instance Num a => Group (Sum a) where
    inv (Sum x) = Sum (negate x)
\end{code}
%<*trans>
\begin{code}
uniq ::  ( Group a
         , Ord a
         , Ord b
         , MonadState (Set b) (t (Heap a))
         , Alternative (t (Heap a)))
     => GraphT a t b -> GraphT a t b
uniq g i = do
    m <- gets (Set.member i)
    guard (not m)
    modify (Set.insert i)
    g i
\end{code}
%</trans>
%<*path>
\begin{code}
path  ::  Functor (t (Heap a))
      =>  GraphT a t b
      ->  GraphT a t [b]
path g xs@(x:_) = fmap (:xs) (g x)
\end{code}
%</path>
%<*dijkstra>
\begin{code}
dijkstra  ::  (Ord a, Group a, Ord b)
          =>  b
          ->  b
          ->  Graph a b
          ->  Maybe [b]
dijkstra f t
  =  fmap reverse
  .  find ((t==) . head)
  .  toList
  .  flip evalStateT Set.empty
  .  flip star [f]
  .  path
  .  uniq 
  .  fmap (lift . fromList)
\end{code}
%</dijkstra>
%<*example>
\begin{code}
graph :: Graph (Sum Int) Int
graph 1  = [(  9,   3  ),(7,   2  ),(14,  6  )]
graph 2  = [(  10,  3  ),(15,  4  ),(7,   1  )]
graph 3  = [(  2,   6  ),(11,  4  ),(9,   1  ),(10,2)]
graph 4  = [(  6,   5  ),(11,  3  ),(15,  2  )]
graph 5  = [(  9,   6  ),(6,   4  )]
graph 6  = [(  9,   5  ),(2,   3  ),(14,  1  )]
graph _  = []
\end{code}

| dijkstra 1 5 graph == Just [1,3,6,5] |
%</example>