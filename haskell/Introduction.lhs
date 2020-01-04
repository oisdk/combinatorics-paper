%include polycode.fmt

%subst keyword a = "\textcolor{BlueViolet}{\textbf{" a "}}"
%format add_2
%format add_3
%options ghci -fglasgow-exts
%format Nat = "\textcolor{OliveGreen}{\mathbb{N}} "
\begin{code}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}

module Introduction where


import Data.Kind (Type)
import Prelude hiding (not, Eq(..), (&&), Maybe(..), Bool(..))
\end{code}
%<*inc>
\begin{code}
inc {-"\underbrace{"-}n{-"}_{\text{argument}}"-} = {-"\underbrace{"-}n + 1{-"}_{\text{body}}"-}
\end{code}
%</inc>
%<*inc-eval>
\indent \verb+>+ | inc 1 | \newline \indent \eval{inc 1}
%</inc-eval>
%<*inc-lambda>
\begin{code}
incl = \ {-"\underbrace{"-}n{-"}_{\text{argument}}"-} -> {-"\underbrace{"-}n + 1{-"}_{\text{body}}"-}
\end{code}
%</inc-lambda>
%<*add>
\begin{code}
add = \ {-"\underbrace{"-}n{-"}_{\text{first argument}}"-} -> \ {-"\underbrace{"-}m{-"}_{\text{second argument}}"-} -> n + m
\end{code}
%</add>
%<*add-eval>
\indent \verb+>+ | add 2 3 | \newline \indent \eval{add 2 3}
%</add-eval>
%<*add-syntax>
\begin{code}
add_2 = \n m -> n + m
add_3 n m = n + m
\end{code}
%</add-syntax>
%<*inc-sig>
\begin{code}
inc :: Integer -> Integer
\end{code}
%</inc-sig>
%<*and>
\begin{code}
and :: Bool -> Bool -> Bool
and  False  False  = False
and  False  True   = False
and  True   False  = False
and  True   True   = True
\end{code}
%</and>
%<*and-op>
\begin{code}
(&&) :: Bool -> Bool -> Bool
False  &&  False  = False
False  &&  True   = False
True   &&  False  = False
True   &&  True   = True
\end{code}
%</and-op>
%<*bool-def>
\begin{code}
data {-"\overbrace{"-}Bool{-"}^{\text{type name}}"-} :: {-"\overbrace{"-}Type{-"}^{\text{kind}}"-} where
  False  :: Bool
  True   :: Bool
\end{code}
%</bool-def>
%<*nat-def>
\begin{code}
data Nat :: Type where
  Zero  :: Nat
  Succ  :: Nat -> Nat
\end{code}
%</nat-def>
%<*nat-example>
\begin{code}
one :: Nat
one = Succ Zero

two :: Nat
two = Succ (Succ Zero)
\end{code}
%</nat-example>
%<*maybe-def>
\begin{code}
data Maybe :: Type -> Type where
  Nothing  :: Maybe a
  Just     :: a -> Maybe a
\end{code}
%</maybe-def>
\begin{code}
deriving instance Show a => Show (Maybe a)
\end{code}
%<*just-one>
\begin{code}
justOne :: Maybe Integer
justOne = Just 1
\end{code}
%</just-one>
%<*is-nothing>
\begin{code}
isNothing :: Maybe a -> Bool
isNothing Nothing = True
isNothing _ = False
\end{code}
%</is-nothing>
%<*make-none>
\begin{code}
makeNothing :: Maybe a
makeNothing = Nothing
\end{code}
%</make-none>
%<*inf-list>
\indent \verb+>+ | take 5 [1..] | \newline \indent \eval{take 5 [1..]}
%</inf-list>
%<*firstEven-sig>
\begin{code}
firstEven :: [Integer] -> Integer
\end{code}
%</firstEven-sig>
\begin{code}
firstEven _ = 0
\end{code}
%<*firstEvenSafe-sig>
\begin{code}
firstEven' :: [Integer] -> Maybe Integer
\end{code}
%</firstEvenSafe-sig>
\begin{code}
firstEven' = foldr (\x xs -> if even x then Just x else xs) Nothing
\end{code}
%<*firstEven-use>
\indent \verb+>+ | firstEven' [1,2,3,4,5] | \newline \indent \eval{firstEven' [1,2,3,4,5]} \newline
\indent \verb+>+ | firstEven' [1,3,5] | \newline \indent \eval{firstEven' [1,3,5]}
%</firstEven-use>
%<*eq-class>
\begin{code}
class {-"\overbrace{"-}Eq{-"}^{\text{class name}}"-} {-"\overbrace{"-}a{-"}^{\text{type parameter}}"-} where
  {-"\underbrace{"-}(==) :: a -> a -> Bool{-"}_{\text{required method}}"-}
\end{code}
%</eq-class>
%<*eq-inst>
\begin{code}
instance Eq Bool where
  False  == False  = True
  False  == True   = False
  True   == False  = False
  True   == True   = True
\end{code}
%</eq-inst>
%<*maybe-inst>
\begin{code}
instance Eq a => Eq (Maybe a) where
  Nothing  == Nothing  = True
  Nothing  == Just _   = False
  Just _   == Nothing  = False
  Just x   == Just y   = x == y
\end{code}
%</maybe-inst>
%<*show-cls>
\begin{code}
class Textual a where
  toText :: a -> String
\end{code}
%</show-cls>
%<*show-inst>
\begin{code}
instance Textual Bool where
  toText True   = "True"
  toText False  = "False"
\end{code}
%</show-inst>
%<*show-deriv>
\begin{code}
instance (Textual a, Textual b) => Textual (a , b) where
  toText (x , y) = "(" ++ toText x ++ ", " ++ toText y ++ ")"
\end{code}
%</show-deriv>
