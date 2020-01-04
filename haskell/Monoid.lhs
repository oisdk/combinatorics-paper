%include polycode.fmt

%subst keyword a = "\textcolor{BlueViolet}{\textbf{" a "}}"
%format mempty = "\epsilon "
%format <> = "\bullet "
\begin{code}
module Monoid where

import Prelude hiding (Monoid(..))
\end{code}

%<*monoid-def>
\begin{code}
class Monoid a where
  mempty  :: a
  (<>)    :: a -> a -> a
\end{code}
%</monoid-def>