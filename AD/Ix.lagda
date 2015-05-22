[2013-2014 Matteo Acerbi](https://www.gnu.org/licenses/gpl.html)

# Indexing into lists

\begin{code}
module AD.Ix where

open import AD.Misc
\end{code}

## `SplitsAs`

First we compute a (small, propositional) predicate corresponding to
the quaternary relation among a (non-empty) list, one of its prefixes,
the element right after that, and the remaining suffix.

\begin{code}
module _ {l}{X : Set l} where

  infix 3 _≣_++_∷_

  _≣_++_∷_ : List X → List X → X → List X → Set
  []       ≣ pref     ++ _ ∷ suff = ⊥
  (x ∷ xs) ≣ []       ++ x̂ ∷ suff = x̂ ≡ x × xs ≡ suff
  (x ∷ xs) ≣ (p ∷ ps) ++ x̂ ∷ suff = x ≡ p × xs ≣ ps ++ x̂ ∷ suff
\end{code}

We also define a synonym to refer to the above family in text.

\begin{code}
  SplitsAs = _≣_++_∷_
\end{code}

We can check the adequacy of the definition of `SplitsAs`.

\begin{code}
  module SplitsAs where

    correct : ∀ {xs ps x ss} → xs ≣ ps ++ x ∷ ss → xs ≡ ps ++ x ∷ ss
    correct {[]    }           ()
    correct {x ∷ xs} {[]}      (<> ,           <>) = <>
    correct {x ∷ xs} {.x ∷ ps} (<> , xs≣ps++x++ss) =
      (_∷_ x) $≡ (correct xs≣ps++x++ss)

    complete : ∀ {xs ps x ss} → xs ≡ ps ++ x ∷ ss → xs ≣ ps ++ x ∷ ss
    complete {ps = []    } <> = <> , <>
    complete {ps = x ∷ ps} <> = <> , complete {ps = ps} <>
\end{code}

Due to UIP, `SplitAs` is a propositional relation.

\begin{code}
    propositional : ∀ {xs ps x ss} → IsProp (xs ≣ ps ++ x ∷ ss)
    propositional {[]    } ()
    propositional {x ∷ xs} {[]     } (<> , <>) (<> , <>) = <>
    propositional {x ∷ xs} {.x ∷ ps} (<> ,  p) (<> ,  q) =
      (_,_ <>) $≡ (propositional {xs}{ps} p q)
\end{code}

## `Ix`

\begin{code}
infix 8 |0_

pattern |1    = inl _
pattern |0_ x = inr x
\end{code}

\begin{code}
pattern Z|    = |1   , <>
pattern S>_ p = |0 _ , p
\end{code}

Small (in the sense of "freely resizable") indices into lists.

\begin{code}
module Ix lI {lX}{X : Set lX} where

  Ix : List X → Set lI
  Ix      []  = ⊥
  Ix (x ∷ xs) = ⊤ {lI} ⊎ Ix xs

  _≟_ : ∀ {xs} → (i j : Ix xs) → Dec (i ≡ j)
  _≟_ {[]    } ()
  _≟_ {x ∷ xs} (inl i) (inl j) = yes , <>
  _≟_ {x ∷ xs} (inl i) (inr j) = no , λ ()
  _≟_ {x ∷ xs} (inr i) (inl j) = no , λ ()
  _≟_ {x ∷ xs} (inr i) (inr j) with i ≟ j
  _≟_ {x ∷ xs} (inr i) (inr ._) | yes , <>  = yes , <>
  _≟_ {x ∷ xs} (inr i) (inr j ) | no  , f   = no  , f ∘ inr-inj where
    inr-inj : ∀ {i j : Ix xs} → inr i ≡ inr j → i ≡ j
    inr-inj <> = <>
\end{code}

`Ix xs` implies that `xs` is non-empty.

\begin{code}
  is∷ : List X → Set lI
  is∷ (_ ∷ _) = ⊤
  is∷      _  = ⊥

  Ix→is∷ : ∀ {xs} → Ix xs → is∷ xs
  Ix→is∷ {[]    } i = i
  Ix→is∷ {x ∷ xs} i = _
\end{code}

A "large" (unresizable) version of `Ix`.

\begin{code}
  IX : List X → Set lX
  IX xs = Σ _ λ ps → Σ _ λ x → Σ _ λ ss → xs ≣ ps ++ x ∷ ss
\end{code}

`Ix xs` and `IX xs` are isomorphic.

\begin{code}
  Ix→IX : ∀ {xs} → Ix xs → IX xs
  Ix→IX {[]    } ()
  Ix→IX {x ∷ xs} (|1  ) = [] , x , xs , <> , <>
  Ix→IX {x ∷ xs} (|0 i) = let ps , y , ss , p = Ix→IX {xs} i in
                          x ∷ ps , y , ss , <> , p

  IX→Ix : ∀ {xs} → IX xs → Ix xs
  IX→Ix {[]    } (_     , _ , _ , ()    )
  IX→Ix {._ ∷ _} ([]    , _ , _ , <> , _) = inl _
  IX→Ix {._ ∷ _} (_ ∷ _ , _ , _ , <> , p) = inr $ IX→Ix (, , , p)
\end{code}

`Ix` is the compressed version.

\begin{code}
  private
    iso₁ : ∀ {xs}(i : Ix xs) → IX→Ix (Ix→IX i) ≡ i
    iso₁ {[]    }    ()
    iso₁ {x ∷ xs} (|1  ) = <>
    iso₁ {x ∷ xs} (|0 i) = inr $≡ iso₁ i
\end{code}

\begin{code}
    module _ {lA}{A : Set lA}{lB}{B : A → Set lB}{lC}{C : Σ _ B → Set lC}{lD}{D : Σ _ C → Set lD} where

      private T = (Σ A λ a → Σ (B a) λ b → Σ (C (a , b)) λ c → D ((a , b) , c))
      _Σ4≡_ : T → T → Set
      (a , b , c , d) Σ4≡ (e , f , g , h) = a ≡ e × b jm≡ f × c jm≡ g × d jm≡ h

      Σ4≡→≡ : ∀ {x y} → x Σ4≡ y → x ≡ y
      Σ4≡→≡ (<> , <> , <> , <>) = <>

    iso₂' : ∀ {xs}(i : IX xs) → Ix→IX (IX→Ix {xs} i) Σ4≡ i
    iso₂' {[]     } (_      , _ ,  _  , ()     )
    iso₂' {._ ∷ _ } ([]     , _ , ._  , <> , <>) = <> , <> , <> , <>
    iso₂' {._ ∷ xs} (y ∷ ys , e ,  zs , <> ,  p) =
      let a , b , c , d = iso₂' {xs} (ys , e , zs , p) in
        _∷_ y $≡ a
      , b
      , c
      ,   Σ≡→≡ (_×_ (y ≡ y) $≡ fst (≡→Σ≡ d)
        , Σ≡→≡ (uip , SplitsAs.propositional {xs = xs} _ _))

    iso₂ : ∀ {xs}(i : IX xs) → Ix→IX (IX→Ix {xs} i) ≡ i
    iso₂ {xs} = Σ4≡→≡ ∘ iso₂' {xs}
\end{code}

\begin{code}
  Ix≅IX : ∀ {xs} → Ix xs Π≅ IX xs
  Ix≅IX {xs} = mk Ix→IX IX→Ix iso₁ (iso₂ {xs})
\end{code}

\begin{code}
  lookup : ∀ {xs} → Ix xs → X
  lookup = fst ∘ snd ∘ Ix→IX

  lookup□ : ∀ {xs lP}{P : X → Set lP}(i : Ix xs) → □List P xs → P (lookup i)
  lookup□ {[]    } () _
  lookup□ {x ∷ xs} (|1  ) (p ,  _) = p
  lookup□ {x ∷ xs} (|0 i) (p , ps) = lookup□ i ps

  prefix suffix : ∀ {xs} → Ix xs → List X
  prefix =             fst ∘ Ix→IX
  suffix = fst ∘ snd ∘ snd ∘ Ix→IX

  − : ∀ {xs} → Ix xs → List X
  − i = prefix i ++ suffix i

  infix 7 _[_/_]

  _[_/_] : ∀ xs → X → Ix xs → List X
  xs [ x / i ] = prefix i ++ x ∷ suffix i

  ix[/_] : ∀ {xs x} → (i : Ix xs) → Ix (xs [ x / i ])
  ix[/_] {[]    } ()
  ix[/_] {x ∷ xs} (|1  ) = |1
  ix[/_] {x ∷ xs} (|0 i) = |0 (ix[/ i ])
\end{code}

\begin{code}
  ⋄List : ∀ {lP}(P : X → Set lP) → List X → Set _
  ⋄List P xs = Σ (Ix xs) (P ∘ lookup)
\end{code}

Membership.

\begin{code}
  infix 3 _∈_

  _∈_ : X → List X → Set lI
  _∈_ = ⋄List ∘ _≡_
\end{code}

\begin{code}
  ∈[/_] : ∀ {xs x} → (i : Ix xs) → x ∈ xs [ x / i ]
  ∈[/_] {[]   } ()
  ∈[/_] {_ ∷ _} (|1  ) = |1 , <>
  ∈[/_] {_ ∷ _} (|0 i) = let j , p = ∈[/_] i in |0 j , p
\end{code}

## Search

\begin{code}
module Search l where

  open Ix l

  instance

    here : ∀ {lA}{A : Set lA}{x : A}{xs} → x ∈ (x ∷ xs)
    here = Z|

    there : ∀ {lA}{A : Set lA}{x y : A}{xs}⦃ p : x ∈ xs ⦄ → x ∈ (y ∷ xs)
    there ⦃ p ⦄ = S> snd p
\end{code}

## Fin

\begin{code}
Fin = Ix.Ix Z ∘ toList
\end{code}
