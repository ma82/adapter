[2013-2014 Matteo Acerbi](https://www.gnu.org/licenses/gpl.html)

# Base definitions

\begin{code}
module AD.Misc where
\end{code}

## Level

\begin{code}
open import Level public
  using    (Level ; _⊔_)
  renaming (zero to Z ; suc to S ; lift to ↑_ ; lower to ↓_)
module Lev = Level

^ = λ {l1} l2 → Level.Lift {l1}{l1 ⊔ l2}

↥_ = λ {l1 l2} → ^ {l1} l2
\end{code}

## Type

\begin{code}
★ = λ l → Set l

★Z = ★ Z
\end{code}

## Dependent product (1)

\begin{code}
open import Function public
  using    (_∘_ ; _∘′_ ; _$_ ; id ; _ˢ_ ; case_of_)
  renaming (flip to _§_)
module Π = Function

K∋ = Π._∋_
syntax  K∋ X x  = x :: X
private test:: = λ l → ★ l :: ★ (S l)

κ : ∀ {lA}{A : ★ lA}{lB}{B : A → ★ lB}(x : A) → B x → A
κ x _ = x

nκ : ∀ {lA}{A : ★ lA}{lB}{B : ★ lB} → A → B → A
nκ x _ = x
\end{code}

## Empty type

Impredicative encoding.

\begin{code}
∅ = λ {l} → {A : Set l} → A
∅Z = ∅ {Z}
\end{code}

Predicative version.

\begin{code}
data ⊥ {l} : ★ l where
⊥Z = ⊥ {Z}

¬_ : ∀ {l} → Set l → Set l
¬ A = A → ⊥Z

⊥-elim : ∀ {l1 l2}{P : ⊥ → ★ l2} → (x : ⊥ {l1}) → P x
⊥-elim ()

magic : ∀ {l1 l2} → ⊥ {l1} → ∅ {l2}
magic = ⊥-elim
\end{code}

## Unit type

\begin{code}
record ⊤ {l} : ★ l where constructor tt
⊤Z  = ⊤ {Z}
\end{code}

## Relations

\begin{code}
open import Relation.Binary public using () renaming
  (Reflexive to IsRefl ; Symmetric to IsSym ; Transitive to IsTrans)
\end{code}

## Equality (identity type)

Impredicative encoding of equality.

\begin{code}
_=[_]=_ : ∀ {lA}{A : Set lA} → A → ∀ lB → A → Set (S lB ⊔ lA)
x =[ lB ]= y = (B : _ → ★ lB) → B x → B y
\end{code}

Standard library's equality.

\begin{code}
open import Relation.Binary.PropositionalEquality public
  using (inspect ; refl) renaming (_≡_ to _==_)
module ≡ = Relation.Binary.PropositionalEquality
\end{code}

As we assume `UIP` anyway, we also add a *small* definition of
equality.

\begin{code}
infix 4 _≡_

data _≡_ {a}{A : Set a}(x : A) : A → Set where
  <> : x ≡ x

Id = λ {l}(A : ★ l) → _≡_ {A = A}
≡_ = _≡_
\end{code}

We would like to pick only this definition but the `rewrite` machinery
apparently does not accept (anymore?) small definitions of equality.

When needed, we will use the following *resizing* workaround.

\begin{code}
to== : ∀ {lA}{A : Set lA}{x y : A} → x ≡ y → x == y
to== <> = refl

from== : ∀ {lA}{A : Set lA}{x y : A} → x == y → x ≡ y
from== refl = <>
\end{code}

We will try to use `_≡_` whenever possible in what follows.

Let us use it to define what being propositional mean for a type, and
prove that equality is indeed propositional.

\begin{code}
IsProp : ∀ {lA} → ★ lA → ★ lA
IsProp A = (x y : A) → x ≡ y

module UIP where

  uip : ∀ {lA}{A : ★ lA}{x y : A} → IsProp (x ≡ y)
  uip <> <> = <>

uip : ∀ {lA}{A : ★ lA}{x y : A}{p q : x ≡ y} → p ≡ q
uip = UIP.uip _ _
\end{code}

### Basic kit for (propositional) equality

\begin{code}
infixr 5 _$≡_

_$≡_ : ∀ {lA lB}{A : ★ lA}{B : ★ lB}(f : A → B){x y} → x ≡ y → f x ≡ f y
f $≡ <> = <>

coe : ∀ {l}{A B : ★ l} → A ≡ B → A → B
coe <> = id
\end{code}

Coercing along equality proofs preserves equality.

\begin{code}
coe-erasable : ∀ {l}{A B : ★ l}(p q : A ≡ B) x → coe p x ≡ coe q x
coe-erasable p q a = Π.flip coe a $≡ uip {p = p}{q}
\end{code}

`rew` (also known as `subst`, `transport`, ...)

\begin{code}
⟦_⟧≡ : ∀ {lA}{A : ★ lA}{x y : A} → x ≡ y → ∀ {lB} → x =[ lB ]= y
⟦ p ⟧≡ B = coe (B $≡ p)

rew : ∀ {lA}{A : ★ lA}{x y : A}{lB}(B : A → ★ lB) → x ≡ y → B x → B y
rew B p = ⟦ p ⟧≡ B
\end{code}

\begin{code}
module _ {lA}{A : Set lA} where

  infixr 4 _⊚_

  _⊚_ : IsTrans (Id A)
  _⊚_ <> = id

  !_ : IsSym (Id A)
  ! <> = <>

import Relation.Binary.EqReasoning as EqR
module ≡R {X : Set} = EqR (record { Carrier = X
                                  ; _≈_ = _≡_
                                  ; isEquivalence = record { refl  = <>
                                                           ; sym   = !_
                                                           ; trans = _⊚_ } })
  hiding (_≡⟨_⟩_) renaming (_≈⟨_⟩_ to _≡⟨_⟩_)

ap₂ : ∀ {lA}{A : ★ lA}{lB}{B : ★ lB}{lC}{C : ★ lC}(f : A → B → C){x w y z} →
      x ≡ y → w ≡ z → f x w ≡ f y z
ap₂ f <> <> = <>
\end{code}

\begin{code}
module J where

  J : ∀ lA lP → Set _
  J lA lP = {A : Set lA}(P : {x y : A} → x ≡ y → Set lP)
            (m : ∀ x → P (<> {x = x})){x y : A}(p : x ≡ y) → P p

  j : {lA lP : _} → J lA lP
  j P m <> = m _
\end{code}

## Isomorphisms

\begin{code}
record Iso-ish {lA }(A : Set lA)
               {l≈A}(_≈A_ : (A → A) → (A → A) → Set l≈A)
               {lB }(B : Set lB)
               {l≈B}(_≈B_ : (B → B) → (B → B) → Set l≈B)
               : Set (lA ⊔ l≈A ⊔ lB ⊔ l≈B) where
  constructor iso
  field to       : A → B
        fr       : B → A
        fr∘to≈id : (fr ∘ to) ≈A id
        to∘fr≈id : (to ∘ fr) ≈B id

infix 1 _≅_

_≅_ : ∀ {lA}(A : Set lA){lB}(B : Set lB) → Set (lA ⊔ lB)
A ≅ B = Iso-ish A _≡_ B _≡_
\end{code}

## Dependent product (2)

\begin{code}
Π : ∀ {l1}(A : ★ l1){l2}(B : A → ★ l2) → ★ (l1 ⊔ l2)
Π A B = ∀ a → B a

Πmap : ∀ {lX lP lQ}{X : ★ lX}{P : X → ★ lP}{Q : X → ★ lQ} →
       (g : ∀ x → P x → Q x) → Π X P → Π X Q
Πmap = _ˢ_

Πpam : ∀ {lA lB lY}{A : ★ lA}{B : ★ lB}{Y : A → ★ lY} →
       (f : B → A) → Π A Y → Π B (Y ∘ f)
Πpam f g = g ∘ f

Πpm : ∀ {lA lB lP lQ}{A : ★ lA}{P : A → ★ lP}{B : ★ lB}{Q : B → ★ lQ} →
        (f : A → B) → {-(Q ∘ f ⇛ P)-} _ → Π B Q → Π A P
Πpm f g = Πmap g ∘ Πpam f
\end{code}

\begin{code}
curly : ∀ {lA}{A : Set lA}{lB}{B : A → Set lB} → Π A B → ({x : A} → B x)
curly f = f _

uncurly : ∀ {lA}{A : Set lA}{lB}{B : A → Set lB} → ({x : A} → B x) → Π A B
uncurly f _ = f
\end{code}

### Dependent product and equality

\begin{code}
module _ {l1}{X : ★ l1}{l2}{Y : X → ★ l2} where

  infix 4 _Π≡_

  _Π≡_ : (f g : Π X Y) → ★ l1
  f Π≡ g = ∀ x → f x ≡ g x

ΠId = λ {l1}{X : ★ l1}{l2}(Y : X → ★ l2) → _Π≡_ {l1}{X}{l2}{Y}

infix 1 _Π≅_

_Π≅_ : ∀ {lA}(A : Set lA){lB}(B : Set lB) → Set (lA ⊔ lB)
A Π≅ B = Iso-ish A _Π≡_ B _Π≡_
\end{code}

Function extensionality

\begin{code}
Ext : ∀ l1 l2 → ★ (S (l1 ⊔ l2))
Ext l1 l2 = {X : ★ l1}{Y : X → ★ l2}{f g : Π X Y} → f Π≡ g → f ≡ g

_Ext_,_→≡_ : ∀ {lA}{A : Set lA} (x : A) l1 l2 (y : A) → ★ _
x Ext l1 , l2 →≡ y = Ext l1 l2 → x ≡ y
\end{code}

\begin{code}
_Ext_,_→≅_ : ∀ {lA}(A : Set lA) l1 l2 {lB}(B : Set lB) → Set _
A Ext l1 , l2 →≅ B = Iso-ish A (λ x y → x Ext l1 , l2 →≡ y)
                             B (λ x y → x Ext l1 , l2 →≡ y)
\end{code}

\begin{code}
↓ext : ∀ {a₁ b₁} a₂ b₂ → Ext (a₁ ⊔ a₂) (b₁ ⊔ b₂) → Ext a₁ b₁
↓ext a₂ b₂ ext f≡g = (λ h → ↓_ ∘ h ∘ ↑_) $≡ ext (_$≡_ (↑_ {ℓ = b₂}) ∘ f≡g ∘ ↓_ {ℓ = a₂})

ext : {{e : ∀ {l1 l2} → Ext l1 l2}} → ∀ {l1 l2} → Ext l1 l2
ext {{e}} = e

txe : ∀ {l1}{X : ★ l1}{l2}{Y : X → ★ l2}{f g : Π X Y} → f ≡ g → f Π≡ g
txe <> _ = <>
\end{code}

## Dependent coproduct

\begin{code}
open import Data.Product public
  using    (Σ ; ∃ ; _×_ ; _,_ ; ,_)
  renaming (proj₁ to fst ; proj₂ to snd ; curry to cu ; uncurry to uc)
module Σ = Data.Product

infix 4 -,_
pattern -,_ x = _ , x

Σmm : ∀ {lA lB lP lQ}
        {A : ★ lA}{B : ★ lB}{P : A → ★ lP}{Q : B → ★ lQ} →
        (f : A → B)(g : ∀ x → P x → Q (f x)) → Σ A P → Σ B Q
Σmm f g = Σ.map f (g _)

×mm : ∀ {lA lB lC lD}
        {A : ★ lA}{B : ★ lB}{C : ★ lC}{D : ★ lD}
        (f : A → B)(g : C → D) → A × C → B × D
×mm f = Σmm f ∘ κ

module Σ-ass {lA}{A : Set lA}{lB}{B : A → Set lB}{lC}{C : Σ _ B → Set lC} where

  private
    L = Σ (Σ A B) λ a,b → C a,b
    R = Σ A λ a → Σ (B a) λ b → C (a , b)

  nestLR : L → R
  nestLR ((a , b) , c) = a , b , c

  nestRL : R → L
  nestRL (a , b , c) = ((a , b) , c)

  ass : L ≅ R
  ass = iso nestLR nestRL <> <>

open Σ-ass public using (nestLR ; nestRL)

module Curry {lA}{A : Set lA}{lB}{B : A → Set lB}{lC}{C : Σ _ B → Set lC} where

  private
    L = Π (Σ A B) λ a,b → C a,b
    R = Π A λ a → Π (B a) λ b → C (a , b)

  currying : Iso-ish L _Π≡_ R (λ f g → ∀ x y → f x y ≡ g x y)
  currying = iso cu uc (λ _ → <>) (λ _ _ → <>)
\end{code}

### Binary coproduct

\begin{code}
open import Data.Sum public
  using    (_⊎_)
  renaming ( inj₁ to inl ; inj₂ to inr ; map to map⊎ )
module ⊎ = Data.Sum

Two : ∀ {l} → ★ l
Two {l} = ⊤ {l} ⊎ ⊤ {l}

TwoZ : Set
TwoZ = Two

pattern true  = inl _
pattern false = inr _

pattern «_ x = true  , x
pattern »_ x = false , x

module _ {lX}{X : ★ lX}{lY}{Y : ★ lY}{lZ}{Z : (X ⊎ Y) → ★ lZ} where

 «-inj : {a : X}{b : Z (inl a)}{c : Z (inl a)} → 
         Id (Σ (X ⊎ Y) Z) (inl a , b) (inl a , c) → b ≡ c
 «-inj <> = <>

 »-inj : {a : Y}{b : Z (inr a)}{c : Z (inr a)} → 
         Id (Σ (X ⊎ Y) Z) (inr a , b) (inr a , c) → b ≡ c
 »-inj <> = <>
\end{code}

### Dependent coproduct and (propositional) equality

\begin{code}
module _ {lA}{A : ★ lA}{lB}{B : A → ★ lB} where

  _Σ≡_ : Σ A B → Σ A B → Set _
  (x , y) Σ≡ (z , w) = Σ (x ≡ z) λ p → rew _ p y ≡ w

  Σ≡→≡ : ∀ {p q} → p Σ≡ q → p  ≡ q
  Σ≡→≡ (<> , <>) =      <>

  ≡→Σ≡ : ∀ {p q} → p  ≡ q → p Σ≡ q
  ≡→Σ≡       <>  = <> , <>

  Σ≡≅≡ : ∀ {p q} → p Σ≡ q Π≅ p ≡ q
  Σ≡≅≡ = iso Σ≡→≡ ≡→Σ≡ fr∘to λ _ → uip where
    fr∘to : ∀ {p q} → ≡→Σ≡ ∘ Σ≡→≡ Π≡ id {A = p Σ≡ q}
    fr∘to (<> , <>) = <>
\end{code}

Logical equivalence, propositional extensionality.

\begin{code}
[★] = λ lA → Σ (★ lA) IsProp

_↔_ : ∀ {lA} → [★] lA → [★] lA → ★ lA
P ↔ Q = (fst P → fst Q) × (fst Q → fst P)

PropExt = λ l → {P Q : [★] l} → P ↔ Q → P ≡ Q
\end{code}

## Pointed types

\begin{code}
★∙ = λ l → Σ (★ l) id

type : ∀ {l} → ★∙ l → Set l
type = fst

element : ∀ {l} → (X,x : ★∙ l) → type X,x
element = snd
\end{code}

### Heterogeneous equality

\begin{code}
_jm≡_ : ∀ {l}{A B : ★ l} → A → B → Set
a jm≡ b = Id (★∙ _) (, a) (, b)
\end{code}

## Predicates (`Pow`)

Contravariant powerset functor.

\begin{code}
Pow : ∀ {lX}(X : ★ lX) l → ★ (S l ⊔ lX)
Pow X l = X → ★ l

Set^  = Pow

infixr 2 _➨_ _⇛_ _⇨_

_⇨_ : ∀ {l1 l2 l3}{I : ★ l1} → Pow I l2 → Pow I l3 → Pow I _
(P ⇨ Q) i = P i → Q i

_➨_ _⇛_ _⇒_ : ∀ {lI lX lY}{I : ★ lI} → Pow I lX → Pow I lY → ★ _
F ➨ G = ∀ {X} → (F ⇨ G) X
X ⇛ Y = Π _ (X ⇨ Y)            
X ⇒ Y = (p : Σ _ X) → Y (fst p) -- <- Hostile to inference (e.g., in `Functor`)

module _ {lX lY lP lQ : _}{X : ★ lX}{Y : ★ lY} where

  _pow>_ : Pow X lP → Pow Y lQ → ★ _
  P pow> Q = Σ (X → Y) λ f → P ⇛ Q ∘ f

module ⇛≅⇒ {lI lX lY}{I : ★ lI}(X : Pow I lX)(Y : Pow I lY) where

  to : X ⇛ Y → X ⇒ Y   ; to = uc
  fr : X ⇒ Y → X ⇛ Y   ; fr = cu
  to∘fr : to ∘ fr ≡ id ; to∘fr = <> -- η Σ Π?
  fr∘to : fr ∘ to ≡ id ; fr∘to = <> -- η Σ Π?
\end{code}

### Dependent product as indexed function

\begin{code}
PowΠ : ∀ {l1 l2}(X : ★ l1) → Pow X l2 → ★ _
PowΠ A B = nκ ⊤Z ⇒ B
\end{code}

\begin{code}
module Π≅PowΠ {lA}(A : ★ lA){lB}(B : Pow A lB) where

  to    : Π A B → PowΠ A B ; to f   = f ∘ fst
  fr    : PowΠ A B → Π A B ; fr f a = f (a , _)
  fr∘to : fr ∘ to ≡ id     ; fr∘to  = <>
  to∘fr : to ∘ fr ≡ id     ; to∘fr  = <>

  Π≅PowΠ : Π A B ≅ PowΠ A B
  Π≅PowΠ = iso to fr fr∘to to∘fr
\end{code}

### `Pow/`

Predicates over indexed types `∀ {i} → X i → Set`.

\begin{code}
Pow/ : ∀ {lI lX}{I : ★ lI}(X : Pow I lX) lP → ★ (S lP ⊔ lX ⊔ lI)
Pow/ X = Pow (Σ _ X)

Set^Σ = Pow/

module _ {lI lX lY lP lQ}{I : ★ lI}{X : Pow I lX}{Y : Pow I lY} where

  _pow/>_ : Pow/ X lP → Pow/ Y lQ → ★ _
  P pow/> Q = Σ (X ⇛ Y) λ f → P ⇛ Q ∘ Σ.< fst , f _ ∘ snd >
\end{code}

\begin{code}
module _ {l1 l2 l3}{I : ★ l1}{X : Pow I l2}{Y : Pow I l3} where

  infix 4 _⇒≡_ _⇛≡_

  _⇒≡_ : (f g : X ⇒ Y) → ★ _
  f ⇒≡ g = f Π≡ g

  _⇛≡_ : (f g : X ⇛ Y) → ★ _
  f ⇛≡ g = (i,x : Σ I X) → let i , x = i,x in f i x ≡ g i x

id⇛ : ∀ {lI lX}{I : ★ lI}{X : Pow I lX} → X ⇛ X
id⇛ i x = x

id⇒ : ∀ {lI lX}{I : ★ lI}{X : Pow I lX} → X ⇒ X
id⇒ = snd

module _ {lI}{I : ★ lI  }
         {lX}{X : Pow I lX}{lY}{Y : Pow I lY}{lZ}{Z : Pow I lZ} where

  infixr 9 _∘⇒_ _∘⇛_ 
       
  _∘⇒_ : (f : Y ⇒ Z)(g : X ⇒ Y) → X ⇒ Z
  f ∘⇒ g = f ∘ ,_ ∘ g ∘ ,_ ∘ snd

  _∘⇛_ : (f : Y ⇛ Z)(g : X ⇛ Y) → X ⇛ Z
  f ∘⇛ g = λ _ → f _ ∘ g _
\end{code}

### ⊥ and ⊤ predicates

\begin{code}
⊥/ : ∀ {l2 l1}{I : ★ l1} → Pow I l2
⊥/ _ = ⊥

⊥Z/ : ∀ {lI}{I : ★ lI} → Pow I Z
⊥Z/ = ⊥/

magic/ : ∀ {l1 l2 l3}{I : ★ l1}{X : Pow I l3} → ⊥/ {l2} ⇛ X
magic/ _ = ⊥-elim

⊤/ : ∀ {l2 l1}{I : ★ l1} → Pow I l2
⊤/ _ = ⊤

⊤Z/ : ∀ {lI}{I : ★ lI} → Pow I Z
⊤Z/ = ⊤/
\end{code}

### Σ and Π over predicates

\begin{code} 
module _ {lI lA lB}{I : ★ lI} where

  Σ/ : (A : Pow I lA)(B : Pow/ A lB) → Pow I _
  Σ/ A B i = Σ (A i) (B ∘ ,_)

  module Σ/ {A : Pow I lA}{B : Pow/ A lB} where

    fst/ : Σ/ A B ⇛ A
    fst/ _ = fst

    snd/ : (i : I)(p : Σ/ A B i) → B (i , fst/ i p)
    snd/ _ = snd

    module _ {lC}{C : Pow/ (Σ/ _ B) lC} where

      cu/ : ∀ i → (Π _ (C ∘ ,_))  → (a : A i)(b : B (, a)) → C (, , b)
      cu/ i f a b = f (a , b)

      uc/ : ∀ i → ((a : A i)(b : B (, a)) → C (, , b)) → (Π _ (C ∘ ,_))
      uc/ i f (a , b) = f a b

  open Σ/ public

  Π/ : (A : Pow I lA)(B : Pow/ A lB) → Pow I _
  Π/ A B i = Π (A i) (B ∘ ,_)

infixr 4 _×/_

_×/_ : ∀ {lI}{I : ★ lI}{lX lY}(X : Pow I lX)(Y : Pow I lY) → I → ★ _
(X ×/ Y) i = X i × Y i
\end{code}

\begin{code}
infixr 3 _⊎/_

_⊎/_ : ∀ {lI lX lY}{I : ★ lI} → Pow I lX → Pow I lY → Pow I _
(X ⊎/ Y) i = X i ⊎ Y i

module ⊎/ {lI lA lB}{I : ★ lI}{A : Pow I lA}{B : Pow I lB} where

  inl/ : A ⇛ A ⊎/ B
  inl/ i = inl

  inr/ : B ⇛ A ⊎/ B
  inr/ i = inr

open ⊎/ public

map⊎/ : {lI lA lB lC lD : _}{I : ★ lI}
        {A : Pow I lA}{B : Pow I lB}{C : Pow I lC}{D : Pow I lD} →
        (A ⇛ C) → (B ⇛ D) → (A ⊎/ B ⇛ C ⊎/ D)
map⊎/ f g n = map⊎ (f n) (g n)

[_,_]/ : {lI lA lB lC : Level}{I : ★ lI}
         {A : Pow I lA}{B : Pow I lB}{C : Pow I lC}
         (α : A ⇛ C)(β : B ⇛ C) → A ⊎/ B ⇛ C
[ α , β ]/ i = ⊎.[ α i , β i ]
\end{code}

## At-key

\begin{code}
module _ {lI}{I : ★ lI} where

  [_:=_] : ∀ {lX} → Pow I lX → I → Pow I lX
  [ X := i ] = ≡ i ×/ X

  [κ_:=_] : ∀ {lX} → ★ lX → I → Pow I lX
  [κ_:=_] X i = [ (λ (i : _) → X) := i ]
\end{code}

## Decidable types

\begin{code}
data Dec? : Set where yes no : Dec?

Dec = λ {l}(X : Set l) → Σ Dec? λ { yes → X ; no  → ¬ X }

module Dec where

  mam : ∀ {l}{X Y : Set l} → (X → Y) → (Y → X) → Dec X → Dec Y
  mam f g (yes ,  x) = yes , f x
  mam f g (no  , ¬x) = no  , ¬x ∘ g
\end{code}

## Functors

\begin{code}
Op : {lO lN : _}(O : ★ lO)(N : ★ lN)(lX lY : _) → ★ _
Op O N lX lY = Pow O lX → Pow N lY
\end{code}

\begin{code}
record RawFunctor {lI}(O N : ★ lI)(lC lD : _) : ★ (S lD ⊔ S lC ⊔ lI) where
  constructor mk
  field
    ∣_∣         : Op O N lC lD
    ∣_∣map      : {A B : Pow O lC} → (A ⇛ B) → ∣_∣ A ⇛ ∣_∣ B
\end{code}

\begin{code}
record Functor {lI}(O N : ★ lI)(lC lD : _) : ★ (S lD ⊔ S lC ⊔ lI) where
  constructor mk

  field
    RF : RawFunctor {lI} O N lC lD

  open RawFunctor RF public

  field
    ∣_∣map-id⇛ : {X : Pow O lC} →
                ∣_∣map id⇛ ⇛≡ id⇛ {X = ∣_∣ X}
    ∣_∣map-∘⇛  : {X Y Z : Pow O lC}{g : X ⇛ Y}{f : Y ⇛ Z} →
                ∣_∣map f ∘⇛ ∣_∣map g ⇛≡ ∣_∣map (f ∘⇛ g)

record FunctorAp {lI}(O N : ★ lI)(lC lD : _) : ★ (S lD ⊔ S lC ⊔ lI) where
  constructor mk

  field
    F : Functor {lI} O N lC lD

  open Functor F public

  field
    ∣_∣map-ap : {X Y : Pow O lC}{f g : X ⇛ Y} → 
               f ⇛≡ g → ∣_∣map f ⇛≡ ∣_∣map g
\end{code}

### Natural transformations

\begin{code}
module NT {lI}{I O : ★ lI} lC lD where

  open RawFunctor

  module Alt where

    _nt>_ = λ (F G : RawFunctor (Set^ I lC × I) (Set^ O lC × O) lC lD) → uc ∣ F ∣ ⇛ uc ∣ G ∣

  _nt>_ = λ (F G : RawFunctor I O lC lD) → ∀ X → ∣ F ∣ X ⇛ ∣ G ∣ X

  natural : (F G : RawFunctor I O lC lD) → F nt> G → ★ _
  natural F G α = ∀ {A B}(f : A ⇛ B) → α B ∘⇛ ∣ F ∣map f Π≡ ∣ G ∣map f ∘⇛ α A

  record _NT>_ (F : RawFunctor I O lC lD)(G : RawFunctor I O lC lD) : ★ (lD ⊔ S lC ⊔ lI) where
    field
      _<$>_ : F nt> G
      isNat : natural F G _<$>_
\end{code}

### Monads

\begin{code}
record IsRawMonad {lI}{I : ★ lI}{lC}(M : Op I I lC lC) : ★ (S lC ⊔ lI) where

  constructor mk

  field
    η    : ∀ {X i} → X i → M X i
    _*   : ∀ {A B} → (A ⇛ M B) → M A ⇛ M B

  module API where

    return : ∀ {X} → X ⇛ M X
    return i = η {i = i}

    join : ∀ {X} i → M (M X) i → M X i
    join = (λ _ → id) *

    _>>=_ : ∀ {A B i} → M A i → (A ⇛ M B) → M B i
    m >>= f = (f *) _ m

    _>>_ : ∀ {A B i} → M A i → (∀ i → M B i) → M B i
    m >> f = m >>= λ i _ → f i

    _=>=_ : ∀ {A B i j} → M [ A := j ] i  →
                   (A j → M B          j) →
                          M B          i
    m =>= f = m >>= λ { ._ (<> , a) → f a }

    rawFunctor : RawFunctor I I lC lC
    rawFunctor = mk M λ f i x → x >>= λ i x → return _ (f i x)

record RawMonad {lI}(I : ★ lI)(lC : _) : ★ (S lC ⊔ lI) where

  constructor mk

  field
    ∥_∥     : Op I I lC lC
    rawMonad : IsRawMonad ∥_∥

  open IsRawMonad rawMonad public hiding (module API)

  module API = IsRawMonad.API rawMonad
\end{code}

TODO. Consider moving this sort of instances to a module of instances
(e.g.: AD.Monad.Instances)

\begin{code}
instance

  fromIsRawMonad : ∀ {lI}{I : ★ lI}{lC}{M : Op I I lC lC}⦃ _ : IsRawMonad M ⦄ → RawMonad I lC
  fromIsRawMonad ⦃ m ⦄ = mk _ m
\end{code}

## Families (`Fam`)

I defined `_⁻¹_` via equality because, before Ulf's `9a4ebdd`, it used
to be the only way to keep it small.

\begin{code}
_⁻¹_ : ∀ {lA lB}{A : ★ lA}{B : ★ lB} → (A → B) → Pow B lA -- (lA ⊔ lB)
f ⁻¹ b = Σ _ λ a → f a ≡ b
\end{code}

Covariant powerset functor.

\begin{code}
Fam : ∀ {lX}(X : ★ lX)(lS : _) → ★ (S lS ⊔ lX)
Fam X lS = Σ (★ lS) λ S → S → X
\end{code}

\begin{code}
Fam/ : ∀ {lI lX}{I : ★ lI}(X : Pow I lX) lP → ★ (S lP ⊔ lX ⊔ lI)
Fam/ X lP = Σ (Pow _ lP) λ S → S ⇛ X
\end{code}

### `Pow/` vs `Fam/`

\begin{code}
toFam/ : ∀ {lI}{I : ★ lI}{lA}{A : Pow I lA}{lP} → Pow/ A lP → Fam/ A (lA ⊔ lP)
toFam/ P = Σ _ ∘ cu P  , fst/

fromFam/ : ∀ {lI}{I : ★ lI}{lA}{A : Pow I lA}{lP} → Fam/ A lP → Pow/ A lP
fromFam/ (X , f) (i , a) = f i ⁻¹ a
\end{code}

`Fam` seems stronger, independently of `_⁻¹_`'s level.

Lifting via `Fam/` and `Pow/` is available for any `Functor`, but
levels are not quite right for many purposes.

\begin{code}
■ : ∀ {lX lI}{O N : ★ lI}(F : Functor O N lX lX)(open Functor) →
    ∀ {X} → Pow/ X lX → Pow/ (∣ F ∣ X) lX
■ F = fromFam/ ∘ ,_ ∘ ∣ F ∣map ∘ snd ∘ toFam/
  where open Functor

all■ : ∀ {lX lI : _}{O N : ★ lI}(F : Functor O N lX lX)(open Functor) →
       {X : Pow O lX}{P : Pow/ X lX} → Π _ P → Π _ (■ F P)
all■ F m (n , xs) = ∣ F ∣map (λ o x → x , m (o , x)) n xs
                  , (∣ F ∣map-∘⇛ (n , xs) ⊚ ∣ F ∣map-id⇛ (n , xs))
  where open Functor
\end{code}

## Abstract nonsense

\begin{code}
module ANS {lO}{O : Set lO}{lN}{N : Set lN}(f : O → N){l} where

  ΔF : Pow N l → Pow O l
  ΔF X = X ∘ f

  ΣF ΠF : Pow O l → Pow N (l ⊔ lO)
  ΣF X n = Σ (f ⁻¹ n) (X ∘ fst)
  ΠF X n = Π (f ⁻¹ n) (X ∘ fst)
\end{code}

## `Maybe`

\begin{code}
open import Data.Maybe public
  using    ()
  renaming (Maybe to 1+_ ; just to ¡ ; nothing to ε)
module 1+ = Data.Maybe
\end{code}

## Lists

\begin{code}
open import Data.List public
      using (List ; [] ; _∷_ ; _++_)
   renaming (map to mapL ; reverse to rev)
module List = Data.List
\end{code}

\begin{code}
module Record {lU}{lEl}(F : Fam (★ lEl) lU) where

  private U = fst F ; El = snd F

  RecordType = List    U
  Record     = List (Σ U El)

module Record★ {l} = Record {lEl = l} (, id)
\end{code}

### □List

\begin{code}
□List : ∀ {lI}{I : ★ lI}{lP} → Pow I lP → Pow (List I) lP
□List P (    []) = ⊤
□List P (i ∷ is) = P i × □List P is
\end{code}

\begin{code}
module □List {lI}{I : ★ lI}{lP}{P : Pow I lP} where

  map : ∀ {lQ}{Q : Pow I lQ} → P ⇛ Q → □List P ⇛ □List Q
  map f []             _  = _
  map f (x ∷ xs) (ps , p) = f x ps , map f xs p

  module _ {lC}{C : Pow (Σ _ (□List P)) lC} where

    elim : C ([] , _) →
           (∀ {x xs p ps} → C (xs , ps) → C (x ∷ xs , p , ps)) →
           ∀ x → C x
    elim m[] m∷ ([]     ,      _) = m[]
    elim m[] m∷ (x ∷ xs , p , ps) = m∷ (elim m[] m∷ (xs , ps))
\end{code}

### Star

\begin{code}
module _ {lA lR : Level}{A : ★ lA} where

  chain : List A → A × A → List (A × A) -- a fold!
  chain []            p  = p ∷ []
  chain (x ∷ xs) (b , e) = (b , x) ∷ chain xs (x , e)

  _[_]✰_ : A → (A → A → ★ lR) → A → ★ _
  x [ R ]✰ y = Σ (List A) (□List (uc R) ∘ chain § (x , y))
\end{code}

## Natural numbers

We could now use lists as natural numbers.

\begin{code}
module List⊤ where

  ℕ = List {Z} ⊤

  pattern zero  = []
  pattern suc n = _ ∷ n

  infixr 4 _+_

  _+_ : ℕ → ℕ → ℕ
  _+_ = _++_

  infixr 5 _*_

  _*_ : ℕ → ℕ → ℕ
  zero  * m = zero
  suc n * m = m + (n * m)

  example :   suc (suc (suc zero)) * (suc (suc zero))
            ≡ suc (suc (suc (suc (suc (suc zero)))))
  example = <>
\end{code}

However, we prefer to maintain the built-in support for natural
numbers, as they support the bidirectional elaboration of numerals and
have an efficient Integer-based implementation.

Therefore, we import the standard library's `Data.Nat`.

\begin{code}
open import Data.Nat public using (ℕ ; zero ; suc ; _+_ ; _*_)
module ℕ = Data.Nat

module _ where private example : 3 * 2 ≡ 6 ; example = <>
\end{code}

\begin{code}
private
  module Ex where
    pattern |0     = ℕ.≤′-refl
    pattern |1+_ x = ℕ.≤′-step x

    example : 0 [ ℕ._≤′_ ]✰ 4
    example =        1 ∷      2 ∷          4 ∷    []
            , |1+ |0 , |1+ |0 , |1+ |1+ |0 , |0 , _
\end{code}

### Vectors

\begin{code}
preds : ℕ → List ℕ -- a para
preds (zero ) = []
preds (suc n) = n ∷ preds n

Down : ∀ {l} → Pow ℕ l → Pow ℕ l
Down X = □List X ∘ preds

Vec : ∀ {l}(X : Set l) → Pow ℕ l
Vec = Down ∘ nκ
\end{code}

\begin{code}
toList : ℕ → List⊤.ℕ
toList = ℕ.fold List⊤.zero List⊤.suc
\end{code}
