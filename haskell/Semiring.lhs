%include polycode.fmt

%subst keyword a = "\textcolor{BlueViolet}{\textbf{" a "}}"
%format * = "\times "
%format one = "1 "
%format zer = "0 "
%format Natural = "\textcolor{OliveGreen}{\mathbb{N}} "
%format gcd = "\text{gcd} "
%format lcm = "\text{lcm} "
%format min = "\text{min} "
%format max = "\text{max} "
%format NInf = "\textcolor{OliveGreen}{\mathbb{N} \cup \{\infty\}} "
%format Inf = "\infty " 
%format Set.union (a) (b) = a "\cup " b
%format Set.empty = "\{\} "
%format Set.singleton (a) = "\{ " a "\} "
%format mempty = "\epsilon "
%format mappend (a) (b) = a "\hcmb " b
\begin{code}
module Semiring where

import Prelude hiding (Num(..))
import Numeric.Natural
import qualified Prelude
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Ratio
\end{code}
%<*class>
\begin{code}
class Semiring a where
    infixl 6 +
    infixl 7 *
    (+), (*) :: a -> a -> a
    one, zer :: a
\end{code}%
%</class>
%<*bool>
\begin{code}
instance Semiring Bool where
    x +   y = x ||  y
    x *   y = x &&  y
    one  = True
    zer  = False
\end{code}
%</bool>
%<*division>
\begin{code}
newtype Division
    = Division { getDivision :: Natural }

instance Semiring Division where
    Division x +  Division y = Division (gcd  x y)
    Division x *  Division y = Division (lcm  x y)
    zer  = Division 0
    one  = Division 1
\end{code}
%</division>
%<*min-plus>
\begin{code}
data NInf = Fin Natural | Inf

instance Semiring NInf where 
    Inf    + y      = y
    x      + Inf    = x
    Fin x  + Fin y  = Fin (min x y)

    Inf     * y      = Inf
    x       * Inf    = Inf
    Fin x   * Fin y  = Fin (x + y)

    zer  = Inf
    one  = Fin 0
\end{code}
%</min-plus>
%{
%format Set.toList (a) = a
%format <- = "\in "
%format [ = "\{ "
%format ] = "\} "
%format Set.fromList (a) = a
%<*set>
\begin{code}
instance (Monoid a, Ord a) =>
                  Semiring (Set a) where
    xs +  ys = Set.union xs ys
    xs *  ys = Set.fromList [ mappend x y | x <- Set.toList xs, y <- Set.toList ys ]
    zer  = Set.empty
    one  = Set.singleton mempty
\end{code}
%</set>
%}
%<*pointwise>
\begin{code}
instance Semiring b => Semiring (a -> b) where
    (f +  g) x = f x +  g x
    (f *  g) x = f x *  g x
    zer  _ = zer
    one  _ = one
\end{code}
%</pointwise>
\begin{code}
instance Semiring Natural where
    (+) = (Prelude.+)
    (*) = (Prelude.*)
    one = 1
    zer = 0

instance Integral a => Semiring (Ratio a) where
    (+) = (Prelude.+)
    (*) = (Prelude.*)
    one = 1
    zer = 0

instance Semiring Integer where
    (+) = (Prelude.+)
    (*) = (Prelude.*)
    one = 1
    zer = 0
\end{code}