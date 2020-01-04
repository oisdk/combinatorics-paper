%include polycode.fmt

%subst keyword a = "\textcolor{BlueViolet}{\textbf{" a "}}"
%format Rational = "\textcolor{OliveGreen}{\mathbb{Q}} "
%format <*> = "\hap "
%format xp = "\mathbb{P}(x) "
%format yp = "\mathbb{P}(y) "
%format coin_1
%format coin_2
%format coin_3
%format frac (a) (b) = "\frac{" a "}{" b "} "
\begin{code}
module Probability where

import Data.Ratio
\end{code}
%<*definition>
\begin{code}
newtype Prob a
    = Prob
    { runProb :: [(a, Rational)]
    }
\end{code}
%</definition>
%<*inst>
\begin{code}
instance Functor Prob where
    fmap f xs = Prob [ (f x, xp) | (x, xp) <- runProb xs ]

instance Applicative Prob where
    pure x = Prob [ (x, 1) ]
    fs <*> xs = do
      f <- fs
      x <- xs
      pure (f x)

instance Monad Prob where
    xs >>= f = Prob  [  (y, xp * yp)
                     |  (x, xp) <- runProb xs
                     ,  (y, yp) <- runProb (f x) ]
\end{code}
%</inst>
%<*expect>
\begin{code}
expect :: (a -> Rational) -> Prob a -> Rational
expect f xs = sum [ f x * xp | (x, xp) <- runProb xs ]
\end{code}
%</expect>
\begin{code}
frac = (/)
\end{code}
%<*coin>
\begin{code}
data Coin = Heads | Tails

coin_1  = Prob [(Heads  , frac 1 2), (Tails  , frac 1 2)]
coin_2  = Prob [(Tails  , frac 1 2), (Heads  , frac 1 2)]
\end{code}
%</coin>
%<*coin-cond>
\begin{code}
coin_3  = Prob [(Heads, frac 1 2), (Tails, frac 1 4), (Tails, frac 1 4)]
\end{code}
%</coin-cond>