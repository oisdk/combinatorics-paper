%include polycode.fmt
%subst keyword a = "\textcolor{BlueViolet}{\textbf{" a "}}"
%format <|> = "\halt "
%format <*> = "\hap "
\begin{code}
  module Monad where

  import Prelude hiding (Applicative(..), Monad(..))
\end{code}
%<*applicative>
\begin{code}
  class Functor f => Applicative f where
    pure   :: a -> f a
    (<*>)  :: f (a -> b) -> f a -> f b

  class Applicative f => Alternative f where
    empty  :: f a
    (<|>)  :: f a -> f a -> f a
\end{code}
%</applicative>
%<*monad>
\begin{code}
  class Applicative f => Monad f where
    (>>=)  :: f a -> (a -> f b) -> f b
  
  class Monad f => MonadPlus f where
    mzero  :: f a
    mplus  :: f a -> f a -> f a
\end{code}
%</monad>