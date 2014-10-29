[2013-2014 Matteo Acerbi](https://www.gnu.org/licenses/gpl.html)

# Manifest

\begin{code}
module AD.Manifest where

open import AD.Misc
\end{code}

In this file we try to use ".." irrelevance because we'd like to make
sure one cannot pattern match on these indices: at the same time,
however, they must not be all identified by conversion, as would
happen by using a single dot "."

(This is how Daniel Gustaffson described ".." to me at ICFP: I hope I
understood correctly, however the feature is not very documented...)

## An *extensible* type of labels

We can mock a type of labels using a type of pointed types.

**Problem**

I cannot do ..x : X.

\begin{code}
-- record Label {lX} : ★ (S lX) where
--   constructor lbl
--   field
--     {X} : ★ lX
-- --  ..x : X
\end{code}

**Problem**

Later uses of `lbl` won't require irrelevance.

\begin{code}
data Label {lX} : ★ (S lX) where
  lbl : {X : ★ lX} → ..(x : X) → Label
\end{code}

`Label` is a large type, which *might* make some *metaprograms*
"larger", but shouldn't affect the universe level of *programs*: these
are meant to only contain inhabitants of `_∋_ Label` (see below), not
of `Label` itself.

## Manifest type

\begin{code}
module Manifest lM where
\end{code}

**Problems**

- If I use ..(a : A) → in the formation rule, I can still not do it
  in the constructor type, or in the following definitions.

- If I use it in both places, I am still not forced to respect this
  polarity in the following definitions! Also, the universe level must
  be raised, for no plausible reason...

\begin{code}
  data _∋_ {lA}(A : ★ lA) : ..(a : A) → ★ {- (lA ⊔ -} lM where
    [_] : {- ..(a : A) -} ∀ a → A ∋ a

  pattern ∙ = [ _ ]
\end{code}

Some handy helpers.

**Problem**

Shouldn't I be *required* to do ..(a : A) → ..(b : B) → here?

\begin{code}
  _+∋_ : ∀ {lA}{A : ★ lA}{lB}{B : ★ lB} → ..(a : A) → ..(b : B) → ★ _
  nl +∋ nr = _ ∋ nl ⊎ _ ∋ nr

  pattern <[_] x = inl [ x ]
  pattern >[_] y = inr [ y ]
  pattern <∙     = <[ ._ ]
  pattern >∙     = >[ ._ ]
\end{code}

Example use: in pattern matching clauses, the dotted patterns will
help identify the case!

**Problem**

Same as above.

\begin{code}
  private
    module Example {A B : ★Z}(f : A → B){x y : A} where

      example∋ : x +∋ y → Σ _ (_∋_ B)
      example∋ <[ .x ] = f x , ∙
      example∋ >[ .y ] = f y , ∙
\end{code}

This only sums labels.

**Problem**

Shouldn't I be *required* to do ..(a : A) → ..(b : B) → here?

\begin{code}
  -- _⊎L_ : ∀ {lX}{A : ★ lX}{lY}{B : ★ lY} → ..(a : A) → ..(b : B) → ★ lM
  _⊎L_ : ∀ {lX}{A : ★ lX}{lY}{B : ★ lY} → A → B → ★ _
  nl ⊎L nr = lbl nl +∋ lbl nr
\end{code}

\begin{code}
  pattern «[_] x = <[ lbl x ]
  pattern »[_] y = >[ lbl y ]

  pattern «∙     = «[ ._ ]
  pattern »∙     = »[ ._ ]
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
    ex1 = «[ val ]

    ex2 : val ⊎L eq
    ex2 = »∙
\end{code}

**Problem**

Shouldn't I be required to write `..(x : ArithLabels) → _`?

(This is a problem with the definition of `Label`, not of `_∋_`)

\begin{code}
    pm-on-labels?! : (x : ArithLabels) → Label ∋ lbl x → TwoZ
    pm-on-labels?! val  x = true
    pm-on-labels?! plus x = false
\end{code}

It seems that at the moment we can still pattern match on labels, and
write "nasty" programs that inspect label arguments: the compiler
won't be able to erase them, in general.
