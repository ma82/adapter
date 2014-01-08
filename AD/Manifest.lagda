## Manifest type

(aka "singleton").

TODO Check terminology.

\begin{code}
module AD.Manifest where

open import AD.Misc
\end{code}

We need a couple of patterns for later.

\begin{code}
pattern «_ x = inl _ , x
pattern »_ x = inr _ , x
\end{code}

\begin{code}
module Manifest lM {lA} where
\end{code}

For "manifest type" of/for `a` we mean the type corresponding to the
proposition that a term `a` has type `A`.

This amounts to requiring something which is already given, so the
type is uninformative (not just propositional but also contractible):
we can obtain it as follows.

\begin{code}
  record _[∋]_ (A : ★ lA)(a : A) : Set lM where
    constructor []

  [[_]] : ∀ {A : ★ lA} → (a : A) → A [∋] a
  [[ a ]] = []
\end{code}

The problem with it being so uninformative, however, is that when we
pattern match on argument of type `A ∋ a` it completely hides the
static inhabitant `a`.

\begin{code}
  module Uninformative {A B}(f : A → B){x y : A} where

    example[∋] : (A [∋] x) ⊎ (A [∋] y) → Σ _ (_[∋]_ B)
\end{code}

Let's first check that while its untyped version would not be wrong
but simply not complete, the following does not typecheck and rightly
so.

\begin{code}
    -- example[∋] (inl l) = , l
    -- example[∋] (inr r) = , r
\end{code}

Thanks to the `η` law for records, any of the following equivalent
versions just work.

\begin{code}
    example[∋] (inl _) = f x , []
    example[∋] (inr _) = f y , []

    -- example[∋] (inl _) = , [[ f x ]]
    -- example[∋] (inr _) = , [[ f y ]]
\end{code}

However, we could implement both cases in the wrong way very easily:
nothing in the lhs gives a hint about what we should be doing (in this
case this is not enforced by the types).

\begin{code}
    -- example[∋] (inl []) = f y , []
    -- example[∋] (inr []) = f x , []
\end{code}

By the way, will the compiled code be strict? I don't know what Agda's
current backends would do, but it *could* still be lazy after seeing
the first bit of the argument.

The problem in the last (wrong) attempts is that we cannot really see
what we are implementing. We would like to have more contextual
information about the problem to be solved (TODO cite).

In this environment, we would actually like to be able to pattern
match as follows.

\begin{code}
--    example[∋] (inl [[ x ]]) = ?
--    example[∋] (inr [[ y ]]) = ?
\end{code}

But that fails for the reason that `[[_]]` is not a pattern.

We can resort to using another inductive family for this purpose.

\begin{code}
  data _∋_ (A : ★ lA) : A → ★ lA where
    [_] : ∀ a → A ∋ a

  [[]] = λ {A : ★ lA}{a : A} → [ a ]
\end{code}

In standard Agda also `A ∋ a` is contractible.

Now we can construct a more readable version.

\begin{code}
  module Readable {A B}(f : A → B){x y : A} where

    example∋ : (A ∋ x) ⊎ (A ∋ y) → Σ _ (_∋_ B)
\end{code}

We can still be lazy on the manifest as before.

\begin{code}
--    example∋ (inl _) = , [ f x ]
--    example∋ (inr _) = , [ f y ]

--    example∋ (inl _) = f x , [[]]
--    example∋ (inr _) = f y , [[]]
\end{code}

If we want to have more readable code, however, we can now pattern
match more deeply.

\begin{code}
    example∋ (inl [ .x ]) = f x , [[]]
    example∋ (inr [ .y ]) = f y , [[]]
\end{code}

We are not finished.

The main problem of the last implementation of `_∋_` is its possibly
large size `★ lA`: sometimes we might want to store inhabitants of
these "unit" types together with other data without ever raising the
universe level.

We can obtain a (hacky) approximation of this by using the first type
as a "code" for the latter, except we do not even need to refer to
that code in the body of the semantic function `>_<`.

\begin{code}
  >_< : ∀ {A}{a : A} → A [∋] a → A ∋ a
  >_< _ = [[]]
\end{code}

Now we can implement the same example as follows.

\begin{code}
  module Hack {A B}(f : A → B){x y : A} where

    example[∋] : (A [∋] x) ⊎ (A [∋] y) → Σ _ λ b → B [∋] b
    example[∋] = help ∘ map⊎ >_< >_< where
      help : A ∋ x ⊎ A ∋ y → Σ _ λ b → B [∋] b
      help (inl [ .x ]) = f x , []
      help (inr [ .y ]) = f y , []
\end{code}

Which is sort of "readable".

The `with` clause does not perform any strict pattern matching, as
shown by the following definitional equality.

\begin{code}
    private test : ∀ {l} → example[∋] (inl l) ≡ f x , []
            test = <>
\end{code}

Some handy helpers.

\begin{code}
  _[!] : {A : ★ lA} → A → Set lM
  a [!] = _ [∋] a

  _+∋_ : {A : ★ lA} → A → A → Set lM
  nl +∋ nr = nl [!] ⊎ nr [!]
\end{code}

