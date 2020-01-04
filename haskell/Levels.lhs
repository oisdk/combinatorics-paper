%include polycode.fmt
%subst keyword a = "\textcolor{BlueViolet}{\textbf{" a "}}"
%format <|> = "\halt "
%format <*> = "\hap "
%format Natural = "\textcolor{OliveGreen}{\mathbb{N}} "
%format sumOver (a) = "\sum_{i = 0}^{\mathopen{|}" a "\mathclose{|}} "
%format x0 = "x_0 "
%format xs1 = "xs_1 "
%format xi = "x_i "
%format y0 = "y_0 "
%format ys1 = "ys_1 "
%format yj = "y_j "
%format zsip1 = "zs_{i+1} "
%format zsij = "zs_{i+j} "
%format zsijp1 = "zs_{i+j+1} "
%format zij = "z_{i+j} "
%format ysip1 = "ys_{i+1} "
%format mul1 (a) (b) = a "\hap " b
%format mul2 (a) (b) = a "\hap " b
%format * = "\times "

%options ghci -fglasgow-exts
\begin{code}
  module Levels where

  import Control.Applicative
  import Numeric.Natural
  import Data.Foldable
  import Control.Monad

  sumOver :: [a] -> (Natural -> a -> [[b]]) -> Levels b
  sumOver xs f = asum (map (Levels . uncurry f) (zip [0..] xs))

  mul1, mul2 :: Levels (a -> b) -> Levels a -> Levels b
\end{code} 
%<*def>
\begin{code}
  newtype Levels a
    = Levels { runLevels :: [[a]] }
\end{code}
%</def>
\begin{code}
  instance Functor Levels where
      fmap f (Levels xs) =
          Levels ((fmap.fmap) f xs)
\end{code}
%<*inst>
\begin{code}
  instance Applicative Levels where
      pure x = Levels [[x]]
      _          <*> Levels [] = Levels []
      Levels xs  <*> Levels (y0:ys1) =
          Levels (foldr f [] xs)
        where
          f xi zsip1 =
              (xi <*> y0) : foldr (g xi) id ys1 zsip1
         
          g xi yj k zsij =
              ((xi <*> yj) ++ zij) : k zsijp1
            where
              ~(zij,zsijp1) = uncons zsij

          uncons []        = ([],[])
          uncons (x0:xs1)  = (x0,xs1)
  
  instance Monad Levels where
      Levels xs >>= k = foldr f empty xs where
        f xi (Levels ysip1) =
          foldr ((<|>) . k) (Levels ([] : ysip1)) xi
\end{code}          
%</inst>
%<*alt>
\begin{code}
  instance Alternative Levels where
      empty = Levels []
      Levels xs <|> Levels ys = Levels (go xs ys)
        where
          go [] ys = ys
          go xs [] = xs
          go (x:xs) (y:ys) = (x ++ y) : go xs ys
\end{code}
%</alt>
%<*mul>
\begin{code}
  delay :: Natural -> [[a]] -> [[a]]
  delay 0  xs = xs
  delay i  xs = [] : delay (i-1) xs

  mul1 (Levels xs) (Levels ys) =
    sumOver xs (\i xi -> delay i (map (xi <*>) ys))
\end{code}
%</mul>
%<*mulf>
\begin{code}
  mul2 (Levels xs) (Levels ys) =
    foldr  (\  xi (Levels zsip1) ->
               Levels (map (xi <*>) ys) <|>
               Levels ([] : zsip1))
           empty
           xs
\end{code}
%</mulf>
\begin{code}
  instance MonadPlus Levels where
  data UpTo a = UpTo Int [a]
  
  instance Show a => Show (UpTo a) where
      showsPrec _ (UpTo i []) s = "[]" ++ s
      showsPrec _ (UpTo i (x:xs)) s = "[" ++ show x ++ foldr f b xs (i-1)
        where
          b _ = ']' : s
          f x xs 0 = "..." ++ s
          f x xs i = ',' : shows x (xs (i-1))

  pythresults = UpTo 5 (concat (runLevels pyth))
\end{code}
\begin{code}
  five x =
\end{code}
%<*five>
\begin{code}
     Levels [[], [], [], [], [], [x]]
\end{code}
%</five>
%<*pyth>
\begin{code}
  pyth :: Levels (Natural,Natural,Natural)
  pyth = do
    x <- Levels (map pure [1..])
    y <- Levels (map pure [1..])
    z <- Levels (map pure [1..])
    guard (x*x + y*y == z*z)
    pure (x,y,z)
\end{code}
| concat (runLevels pyth) == | \newline
\eval{pythresults}
%</pyth>