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
  module PairingHeap.Listed where
  import Control.Monad (ap)
\end{code}
%<*def>
\begin{code}
  newtype Greedy a b
      =  Greedy
      {  runGreedy :: [(a, b)]
      }
\end{code}
%</def>
%<*merge>
\begin{code}
  merge  ::  Ord a
         =>  [(a,b)]
         ->  [(a,b)]
         ->  [(a,b)]
  merge [] ys           = ys
  merge ((x,xv):xs) ys  = go x xv xs ys
    where
      go x xv xs [] = (x,xv) : xs
      go x xv xs ((y,yv):ys)
        | x <= y     = (x,xv) : go y yv ys xs
        | otherwise  = (y,yv) : go x xv xs ys
        
  instance Ord a
        => Semigroup (Greedy a b) where
   Greedy xs <> Greedy ys =
     Greedy (merge xs ys)
          
  instance Ord a => Monoid (Greedy a b) where
      mempty = Greedy []
\end{code}
%</merge>
%<*monad>
\begin{code}
  instance Functor (Greedy a) where
    fmap f (Greedy xs) =
      Greedy ((fmap.fmap) f xs)
    
  instance (Ord a, Monoid a)
      => Applicative (Greedy a) where    
    pure x = Greedy [(mempty, x)]
    (<*>) = ap
      
  (<><)  ::  Semigroup a
         =>  a
         ->  Greedy a b
         ->  Greedy a b
  x <>< Greedy xs = Greedy  [  (x <> w, y)
                            |  (w,y) <- xs ]
  
  instance (Ord a, Monoid a)
      => Monad (Greedy a) where
    Greedy xs >>= f =
      foldMap (\(w,x) -> w <>< f x) xs
\end{code}
%</monad>
\begin{code}
  unopt x y z =
\end{code}
%<*unopt>
\begin{code}
    [(1, x), (5, y), (7, z)]
\end{code}
%</unopt>
\begin{code}
  opt x y z =
\end{code}
%<*opt>
\begin{code}
    [(1, x), (4, y), (2, z)]
\end{code}
%</opt>