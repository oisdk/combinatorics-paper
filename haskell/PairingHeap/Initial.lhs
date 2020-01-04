%include polycode.fmt
%subst keyword a = "\textcolor{BlueViolet}{\textbf{" a "}}"
%format <> = "\hcmb "
%format x1 = "x_1"
%format x2 = "x_2"
%format x3 = "x_3"
%format mconcat = "\sum "
%format mempty = "\epsilon "
\begin{code}
  module PairingHeap.Initial where

  import Data.Semigroup
  import Data.List (unfoldr)
\end{code}
%<*heap>
\begin{code}
  data Heap a
      = Leaf
      | Node a [Heap a]

  instance Ord a => Semigroup (Heap a) where
      Leaf <> ys  = ys
      xs <> Leaf  = xs
      xh@(Node x xs) <> yh@(Node y ys)
        | x <= y     = Node x (yh : xs)
        | otherwise  = Node y (xh : ys)

  instance Ord a => Monoid (Heap a) where
      mempty = Leaf
      mconcat [] = Leaf
      mconcat (x : xs) = go x xs where
        go x []               = x
        go x1 (x2 : [])       = x1 <> x2
        go x1 (x2 : x3 : xs)  = (x1 <> x2) <> go x3 xs

  popMin  ::  Ord a
          =>  Heap a
          ->  Maybe (a, Heap a)
  popMin Leaf         = Nothing
  popMin (Node x xs)  = Just (x, mconcat xs)

  singleton :: a -> Heap a
  singleton x = Node x []

  sort :: Ord a => [a] -> [a]
  sort = unfoldr popMin . foldMap singleton
\end{code}
%</heap>