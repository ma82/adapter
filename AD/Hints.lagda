# Instances

Hinting instance search with lists of pointed types.

\begin{code}
module AD.Hints {l} where

open import AD.Ix; open Ix l; open Search l
open import AD.Misc ; open Record★
\end{code}

\begin{code}
private
 module Test {A : Set l}(a b c : A) where

  example : ⦃ p : a ∈ b ∷ a ∷ c ∷ [] ⦄ → TwoZ
  example ⦃ inl p       , _ ⦄ = inl _
  example ⦃ inr (inl p) , _ ⦄ = inr _
  example ⦃ inr (inr p) , _ ⦄ = inl _

  test : example ≡ inr _
  test = <>
\end{code}

\begin{code}
infix 0 |||_

record |||_ (X : Set l) : Set l where
  field km : X 
open |||_ public

module Hints (Xs : Record) where

  instance

    hint : ∀ {X x}⦃ p : (X , x) ∈ Xs ⦄ → ||| X
    hint { x = x } = record { km = x }

  # : ∀ {X x}⦃ p : (X , x) ∈ Xs ⦄ → X
  # = km hint
\end{code}

The idea is that now, opening `Hints Xs` for some record `Xs`, we can
hint instance search with all the pointed types in `Xs`, whatever its
length.

\begin{code}
module Test2 where

  data N : Set l where ze : N ; su : N → N

  exampleRecord : Record
  exampleRecord = (N , su (su ze)) ∷ (N , ze) ∷ (Two , true) ∷ []

  open Hints exampleRecord

  test1 : # ≡ ze
  test1 = <>

  test2 : # ≡ su (su ze)
  test2 = <>

  test3 : # ≡ true
  test3 = <>
\end{code}
