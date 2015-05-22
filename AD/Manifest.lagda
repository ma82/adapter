[2013-2014 Matteo Acerbi](https://www.gnu.org/licenses/gpl.html)

# Manifest

TODO Better rename as "singleton"

\begin{code}
module AD.Manifest where

open import AD.Misc
\end{code}

## An *extensible* type of labels

We use a type of pointed types as an extensible type of "labels".

\begin{code}
data Label {lX} : ★ (S lX) where
  lbl : {X : ★ lX} → (x : X) → Label
\end{code}

## Manifest type

\begin{code}
module Manifest lM where
\end{code}

I desired `_∋_` to be at level `lM`, but it would make Agda
[inconsistent with
EM](https://lists.chalmers.se/pipermail/agda/2015/007381.html).

\begin{code}
  module Large where

    infix 5 _∋_

    data _∋_ {lA}(A : ★ lA) : (a : A) → ★ (lA ⊔ lM) {- ★ lM -} where
      [_] : (a : A) → A ∋ a

    pattern ∙ = [ _ ]

    pattern <[_] x = inl [ x ]
    pattern >[_] y = inr [ y ]
    pattern <∙     = <[ ._ ]
    pattern >∙     = >[ ._ ]

    pattern «[_] x = <[ lbl x ]
    pattern »[_] y = >[ lbl y ]

    pattern «∙ = «[ ._ ]
    pattern »∙ = »[ ._ ]

    _+∋_ : ∀ {lA}{A : ★ lA}{lB}{B : ★ lB} → A → B → ★ _
    nl +∋ nr = _ ∋ nl ⊎ _ ∋ nr
\end{code}

This only sums labels.

\begin{code}
    _⊎L_ : ∀ {lX}{A : ★ lX}{lY}{B : ★ lY} → A → B → ★ _
    nl ⊎L nr = lbl nl +∋ lbl nr
\end{code}

Example usage.

\begin{code}
    private
      module LabelsÀLaCarte where

        data ArithLabels : ★Z where
          val plus : ArithLabels

        data LogicLabels : ★Z where
          ite eq : LogicLabels

        ex1 : val ⊎L eq
        ex1 = «[ val ]

        ex2 : val ⊎L eq
        ex2 = »∙
\end{code}

Example use: in pattern matching clauses, the dotted patterns will
help identify the case!

\begin{code}
    private
      module Example {A B : ★Z}(f : A → B){x y : A} where

        example∋ : x +∋ y → Σ _ (_∋_ B)
        example∋ <[ .x ] = f x , ∙
        example∋ >[ .y ] = f y , ∙
\end{code}

I will go back to faking it.

\begin{code}
  infix 5 _∋_

  record _∋_ {lA}(A : ★ lA)(a : A) : ★ lM where
    constructor ∙

  [_] : ∀ {lA}{A : ★ lA}(a : A) → A ∋ a
  [ _ ] = ∙

  _+∋_ : ∀ {lA}{A : ★ lA}{lB}{B : ★ lB} → A → B → ★ _
  nl +∋ nr = _ ∋ nl ⊎ _ ∋ nr
\end{code}

A view I won't probably use. The idea is that you can get "more
readable" code by "with zoom∋ x".

\begin{code}
  zoom∋ : ∀ {lA}{A : ★ lA}{a} → A ∋ a → A Large.∋ a
  zoom∋ _ = Large.∙
\end{code}

This only sums labels.

\begin{code}
  _⊎L_ : ∀ {lX}{A : ★ lX}{lY}{B : ★ lY} → A → B → ★ _
  nl ⊎L nr = lbl nl +∋ lbl nr
\end{code}

Example usage of manifests with labels.

\begin{code}
private
  module LabelsÀLaCarte where

    open Manifest Z

    data ArithLabels : ★Z where
      val plus : ArithLabels

    data LogicLabels : ★Z where
      ite eq : LogicLabels

    ex1 : val ⊎L eq
    ex1 = inl ∙

    ex2 : val ⊎L eq
    ex2 = inr ∙
\end{code}
