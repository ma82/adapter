[2013-2014 Matteo Acerbi](https://www.gnu.org/licenses/gpl.html)

# Binary trees with labeled nodes and leafs

\begin{code}
module AD.TagTree where

open import AD.Misc
open import AD.Manifest

module Tree {lA}(A : ★ lA) where

  mutual
    Tree► = Σ A λ a → Tree▻

    data Tree▻ : ★ lA where
      []   :                 Tree▻
      _**_ : Tree► → Tree► → Tree▻
\end{code}

Given a `Tree►` we can compute the type of paths from its root to any
of its subtrees.

The semantics only considers the tags of children of every node, as if
we had only tagged the edges.

\begin{code}
module ⟦⟧Tree {lA}{A : ★ lA}{lI : Level} where

  open Tree A ; open Manifest lI {lA}

  ⟦_⟧Tree▻ : Tree▻ → ★ lI
  ⟦ []                 ⟧Tree▻ = ⊤
  ⟦ (a , l) ** (b , r) ⟧Tree▻ = Σ (a +∋ b)
                                  ⊎.[ nκ ⟦ l ⟧Tree▻ , nκ ⟦ r ⟧Tree▻ ]

  ⟦_⟧Tree► : Tree► → ★ lI
  ⟦ _ , t ⟧Tree► = ⟦ t ⟧Tree▻
\end{code}

The meaning of a `Tree►` is a set of finite bitstrings. Each of them
denotes the turns that need to be taken to walk the path from the root
of the tree to a particular subtree. The set contains the bitstrings
corresponding to all the subtrees.

While this semantics also contains names from `A`, they are not needed
at runtime because anything of type `A ∋ a` for some `A` and `a` is
propositional, hence erasable: the compiler should delete them, and
probably some of Agda's backends already do (TODO Check... Ask?).

TODO Needed?

\begin{code}
  [_,_]Tree : {l lC : Level}{I : ★ lI}{m n : A}
              {A B : Pow I l}{C : Pow I lC}
              (α : A ⇛ C)(β : B ⇛ C) →
              ∀ i → Σ (m +∋ n) ⊎.[ κ (A i) , κ (B i) ] → C i
  [ α , β ]Tree i = uc ⊎.[ κ (α i) , κ (β i) ]
\end{code}

\begin{code}
pattern injL a b = « a , b
pattern injR a b = » a , b
\end{code}

