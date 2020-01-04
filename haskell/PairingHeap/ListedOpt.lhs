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
  module PairingHeap.ListedOpt where

  import Group
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
  merge  ::  (Ord a, Group a)
         =>  [(a,b)]
         ->  [(a,b)]
         ->  [(a,b)]
  merge [] ys           = ys
  merge ((x,xv):xs) ys  = go x xv xs ys
    where
      go x xv xs [] = (x,xv) : xs
      go x xv xs ((y,yv):ys)
        | x <= y     =
          (x,xv) : go (inv x <> y) yv ys xs
        | otherwise  =
          (y,yv) : go (inv y <> x) xv xs ys
\end{code}
%</merge>
%<*mulin>
\begin{code}
  (<><)  ::  Semigroup a
         =>  a
         ->  Greedy a b
         ->  Greedy a b
  x <>< Greedy []          = Greedy []
  x <>< Greedy ((w,y):ys)  =
    Greedy ((x <> w, y) : ys)
\end{code}
%</mulin>