%include polycode.fmt

%subst keyword a = "\textcolor{BlueViolet}{\textbf{" a "}}"
%format mempty = "\epsilon "
%format <> = "\bullet "
%format . = "."
%format forall = "\forall "
\begin{code}
{-# LANGUAGE ExistentialQuantification #-}
module MonoidExt where

import Prelude hiding (Monoid(..))
\end{code}
%<*monoid-ext>
\begin{code}
data Monoid
    = forall a. Monoid { mempty  :: a, (<>) :: a -> a -> a }
\end{code}
%</monoid-ext>