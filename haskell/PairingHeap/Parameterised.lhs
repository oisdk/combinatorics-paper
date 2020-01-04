%include polycode.fmt
%subst keyword a = "\textcolor{BlueViolet}{\textbf{" a "}}"
%format <> = "\hcmb "
%format x1 = "x_1"
%format x2 = "x_2"
%format x3 = "x_3"
%format <*> = "\hap "
%format <>< = "\hcmbin "
%format mconcat = "\sum "
%format mempty = "\epsilon "
\begin{code}
  module PairingHeap.Parameterised where

  import Data.Semigroup
\end{code}
%<*heap>
\begin{code}
  data Heap a b
      =  Leaf
      |  Node a b [Heap a b]
\end{code}
%</heap>
\begin{code}
  instance Ord a => Semigroup (Heap a b) where
      Leaf <> ys  = ys
      xs <> Leaf  = xs
      xh@(Node x xv xs) <> yh@(Node y yv ys)
        | x <= y     = Node x xv (yh : xs)
        | otherwise  = Node y yv (xh : ys)

  instance Ord a => Monoid (Heap a b) where
      mempty = Leaf
      mconcat [] = Leaf
      mconcat (x : xs) = go x xs where
        go x []               = x
        go x1 (x2 : [])       = x1 <> x2
        go x1 (x2 : x3 : xs)  = (x1 <> x2) <> go x3 xs

  popMin  ::  Ord a
          =>  Heap a b
          ->  Maybe ((a, b), Heap a b)
  popMin Leaf            = Nothing
  popMin (Node x xv xs)  =
    Just ((x, xv), mconcat xs)
\end{code}
%<*singleton>
\begin{code}
  singleton  ::  Monoid a
             =>  b
             ->  Heap a b
  singleton x = Node mempty x []
\end{code}
%</singleton>
\begin{code}
  instance Functor (Heap a) where
      fmap f Leaf = Leaf
      fmap f (Node k x xs) =
        Node k (f x) (map (fmap f) xs)

  instance (Ord a, Monoid a)
          => Applicative (Heap a) where
      pure = singleton
      fs <*> xs =  fs >>= \f ->
                   xs >>= \x ->
                   pure (f x)
\end{code}                   
%<*monad>
\begin{code}
  (<><) :: Monoid a => a -> Heap a b -> Heap a b
  x <>< Leaf          = Leaf
  x <>< Node y yv ys  =
    Node (x <> y) yv (map (x <><) ys)

  instance (Ord a, Monoid a)
          => Monad (Heap a) where
      Leaf >>= f = Leaf
      Node k x xs >>= f = 
        (k <>< f x) <> mconcat (map (>>= f) xs)
\end{code}
%</monad>
\begin{code}
  exampleTree1 =
\end{code}
%<*nonopttree>
\begin{code}
    Node 2 ()  [  Node 3  () []
               ,  Node 4  () []
               ,  Node 2  () [] ]
\end{code}
%</nonopttree>
\begin{code}
  exampleTree2 =
\end{code}
%<*opttree>
\begin{code}
    Node 2 ()  [  Node 1  () []
               ,  Node 2  () []
               ,  Node 0  () [] ]
\end{code}
%</opttree>