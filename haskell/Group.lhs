%include polycode.fmt
%subst keyword a = "\textcolor{BlueViolet}{\textbf{" a "}}"
%format inv (a) = a "^{-1} "
\begin{code}
  module Group where
\end{code}
%<*def>
\begin{code}
  class Monoid a => Group a where
      inv :: a -> a
\end{code}
%</def>