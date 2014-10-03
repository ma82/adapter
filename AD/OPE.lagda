[2013-2014 Matteo Acerbi](https://www.gnu.org/licenses/gpl.html)

# Order-preserving embeddings

TODO. Move to AD.Sub or AD.List.Sub or similar, as there are now other
constructions based on Sub.

\begin{code}
module AD.OPE where

open import AD.Misc
open import AD.Ix
\end{code}

TODO. Patterns for Two instead.

\begin{code}
data Embed? : Set where keep skip : Embed?

−Embed? : Embed? → Embed?
−Embed? keep = skip
−Embed? skip = keep
\end{code}

## `Sub`

\begin{code}
module _ {l}{X : Set l} where

  Sub : List X → Set
  Sub = □List λ _ → Embed?

  −sub : ∀ {xs} → Sub xs → Sub xs
  −sub = □List.map (nκ −Embed?) _

  ⟦_⟧Sub : ∀ {xs} → Sub xs → List X
  ⟦_⟧Sub {[]}     p          = []
  ⟦_⟧Sub {x ∷ xs} (keep , p) = x ∷ ⟦ p ⟧Sub
  ⟦_⟧Sub {x ∷ xs} (skip , p) = ⟦ p ⟧Sub
\end{code}

[Ix] and Sub.

\begin{code}
  module _ {l} where

    open Ix l

    _Sub∋_ : ∀ {xs}(s : Sub xs)(j : Ix xs) → Set
    _Sub∋_ {[]    } s           ()
    _Sub∋_ {x ∷ xs} (keep , _) (|1  ) = ⊤
    _Sub∋_ {x ∷ xs} (skip , _) (|1  ) = ⊥
    _Sub∋_ {x ∷ xs} (e    , s) (|0 p) = s Sub∋ p

    sub− : ∀ {xs}(s : Sub xs){j : Ix xs} → Sub (− j)
    sub− {[]    }(    s) {}
    sub− {x ∷ xs}(_ , s) {|1  } = s
    sub− {x ∷ xs}(e , s) {|0 p} = e , sub− s
\end{code}

## `_<∷_` (OPE)

\begin{code}
  infix 4 _<∷_

  _<∷_ : List X → List X → Set
  xs <∷ ys = Σ (Sub ys) λ < → ⟦ < ⟧Sub ≡ xs
\end{code}

These morphisms are known as [order-preserving
embeddings](http://sneezy.cs.nott.ac.uk/fplunch/weblog/?p=91).

TODO Prove they preserve `_⊢_<<_`!

TODO Clean-up

We prefer to obtain OPEs in this way and not by an inductive family
with two indices because, by also adopting the small equality `_≡_`,
this allows us to have both the type of order-preserving sublists and
the one of order-preserving embeddings, independently of the size of
`X`.

In our encoding of inductive types this will allow OPEs between lists
of tags of *any* size to be stored together with the data, without
ever raising any universe level.

## Properties of `Sub` and `_<∷_`

### Reflexivity/Identity

\begin{code}
module _ {l}{X : Set l} where
  const : Embed? → (xs : List X) → Sub xs
  const _ []       = tt
  const e (x ∷ xs) = e , const e xs

  idSub = const keep

  ⟦⟧∘idSub≡id : ∀ {xs} → ⟦ idSub xs ⟧Sub ≡ xs
  ⟦⟧∘idSub≡id {[]    } = <>
  ⟦⟧∘idSub≡id {x ∷ xs} = (_∷_ x) $≡ ⟦⟧∘idSub≡id

  <∷> : IsRefl _<∷_
  <∷> {xs} = const keep xs , ⟦⟧∘idSub≡id
\end{code}

### Transitivity/Composition

TODO Sub seems a *relative* monad, check the details.

TODO Implement _>>=Sub_ from _<∷∘_ ? 

\begin{code}
  _>>=Sub_ : {xs ys : List X} → (s : Sub xs) → xs <∷ ys → Sub ys

  _>>=Sub_ {[]} {ys} _ q = fst q
  _>>=Sub_ {x ∷ xs}{[]} _ _ = tt

  _>>=Sub_ {x ∷ ._}{.x ∷ ys} (keep , q) ((keep , r) , <>) = keep , q >>=Sub (r , <>)
  _>>=Sub_ {x ∷ ._}{.x ∷ ys} (skip , q) ((keep , r) , <>) = skip , q >>=Sub (r , <>)
  _>>=Sub_ {x ∷ xs}{ y ∷ ys} p          ((skip , r) , s ) = let z = p >>=Sub (r , s) in
                                                            skip , z
\end{code}

\begin{code}
  lem : ∀ xs → ⟦ const skip xs ⟧Sub ≡ []
  lem (    []) = <>
  lem (x ∷ xs) = lem xs

  _<∷∘_ : {xs ys zs : List X} → xs <∷ ys → ys <∷ zs → xs <∷ zs
  _<∷∘_ {[]}     {ys     } {zs} _       _        = const skip zs , lem zs
  _<∷∘_ {x ∷ xs} {[]     } {zs} (p , r) q        = ⟦ r ⟧≡ (_<∷_ § zs) q
  _<∷∘_ {x ∷ xs} {y  ∷ ys} {[]} _       (_ , ())
  _<∷∘_ {x ∷ ._} {.x ∷ ._} {.x ∷ zs} ((keep , q) , <>) ((keep , s) , <>) = 
    let z , w = (q , <>) <∷∘ (s , <>) in
    (keep , z) , (_∷_ x) $≡ w
  _<∷∘_ {x ∷ xs} {y  ∷ ._} {.y ∷ zs} ((skip , q) ,  r) ((keep , s) , <>) =
    let z , w = (q , r)  <∷∘ (s , <>) in
    (skip , z) , w
  _<∷∘_ {x ∷ xs} {y  ∷ ys} {z  ∷ zs}                p  ((skip , r) ,  s) =
    let z , w = p <∷∘ (r , s) in
    (skip , z) , w
\end{code}

### Relevance

Note that this `_<∷_` is not a propositional relation, for example we
have two different OPEs of type

    [1,2] <∷ [1,1,2,3]

\begin{code}
private
  test1 : (1 ∷ 2 ∷ []) <∷ 1 ∷ 1 ∷ 2 ∷ 3 ∷ []
  test1 = (keep , skip , keep , skip , _) , <>

  test2 : (1 ∷ 2 ∷ []) <∷ 1 ∷ 1 ∷ 2 ∷ 3 ∷ []
  test2 = (skip , keep , keep , skip , _) , <>
\end{code}

\begin{code}
not-prop : (∀ {l}{X : Set l}{xs ys : List X} → IsProp (xs <∷ ys)) → ⊥Z
not-prop f with f test1 test2
not-prop f | ()
\end{code}

TODO Category laws

TODO Antisymmetry should also hold, I guess.

TODO IIRC in some sources (Awodey?) partial orders are required to be
propositional, so this would not be one. Maybe it would be for lists
without duplicates: any pair of such lists should admit at most one
order-preserving embedding.

