# Instances

Feeding lists of pointed types to Guillaume's recursive instance
search machinery.

\begin{code}
module AD.Instances {l} where

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
record Instance (X : Set l) : Set l where
  field km : X 
open Instance public

module Instances (Xs : Record) where

  instance

    inst : ∀ {X x}⦃ p : (X , x) ∈ Xs ⦄ → Instance X
    inst { x = x } = record { km = x }

  # : ∀ {X x}⦃ p : (X , x) ∈ Xs ⦄ → X
  # = km inst
\end{code}

The idea is that now, opening `Instances Xs` for some record `Xs`, we
can hint instance search with all the pointed types in `Xs`, whatever
its length.

\begin{code}
module Test2 where

  data N : Set l where ze : N ; su : N → N

  exampleRecord : Record
  exampleRecord = (N , su (su ze)) ∷ (N , ze) ∷ (Two , true) ∷ []

  open Instances exampleRecord

  test1 : # ≡ ze
  test1 = <>

  test2 : # ≡ su (su ze)
  test2 = <>

  test3 : # ≡ true
  test3 = <>
\end{code}
