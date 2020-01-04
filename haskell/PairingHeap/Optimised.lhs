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
\begin{code}
  module PairingHeap.Optimised where

  import Group

  data Heap a b
      =  Leaf
      |  Node a b [Heap a b]
\end{code}
%<*merge>
\begin{code}
  instance (Ord a, Group a)
        => Semigroup (Heap a b) where
    Leaf <> ys = ys
    xs <> Leaf = xs
    Node x xv xs <> Node y yv ys
      | x <= y     =  Node x xv
                      (Node (inv x <> y) yv ys : xs)
      | otherwise  =  Node y yv
                      (Node (inv y <> x) xv xs : ys)
\end{code}
%</merge>
\begin{code}
  instance (Ord a, Group a)
        => Monoid (Heap a b) where
    mempty = Leaf
    mconcat [] = Leaf
    mconcat (x : xs) = go x xs where
      go x [] = x
      go x1 (x2 : []) = x1 <> x2
      go x1 (x2 : x3 : xs) = (x1 <> x2) <> go x3 xs
\end{code}
%<*cmbin>
\begin{code}
  (<><)   ::   Semigroup a
          =>   a
          ->   Heap a b
          ->   Heap a b
  x <>< Leaf = Leaf
  x <>< Node y yv ys = Node (x <> y) yv ys
\end{code}
%</cmbin>
\begin{code}
  instance Functor (Heap a) where
    fmap f Leaf = Leaf
    fmap f (Node xk x xs)
      = Node xk (f x) (map (fmap f) xs)
    
  instance (Ord a, Group a)
      => Applicative (Heap a) where
    pure x = Node mempty x []
    fs <*> xs =  fs >>= \f ->
                 xs >>= \x ->
                 pure (f x)
\end{code}                      
%<*mon>
\begin{code}
  instance (Ord a, Group a)
      => Monad (Heap a) where
    Leaf >>= _ = Leaf
    Node k x xs >>= f =
      k <>< (mconcat (map (>>= f) xs) <> f x)
\end{code}
%</mon>