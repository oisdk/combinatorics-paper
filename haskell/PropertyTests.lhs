%include polycode.fmt
\begin{code}
module PropertyTests where
\end{code}
%<*sort-stable>
\begin{code}
propStable :: [(Int,Bool)] -> Property
propStable xs =
  map fst (sortOn snd xs) ==  [ x | (x,False  ) <- xs] ++
                              [ x | (x,True   ) <- xs]
\end{code}
%</sort-stable>