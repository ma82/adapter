[2013-2014 Matteo Acerbi](https://www.gnu.org/licenses/gpl.html)

# Base definitions

TODO <2014-01-08 Wed>
Modularise some more. E.g., make independent modules for List, Pow, Fam ...

TODO <2013-11-29 Fri>
Notational convention for indexed things is a bit incoherent.
Back to trailing slash?

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
module Type l where ★ = Set l

open Type public
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

\begin{code}
data   ⊥ {l} : ★ l where
[0]  = ⊥ {Z}

¬_ : ∀ {l} → Set l → Set l
¬ A = A → [0]

⊥-elim : ∀ {l1 l2}{P : ⊥ → ★ l2} → (x : ⊥ {l1}) → P x
⊥-elim ()

magic : ∀ {l1 l2}{A : ★ l2} → ⊥ {l1} → A
magic = ⊥-elim
\end{code}

## Unit type

\begin{code}
record ⊤ {l} : ★ l where constructor tt
[1]  = ⊤ {Z}
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

TODO Remove cong

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

TODO Remove cong₂
TODO Derive ap₂ from Σ≡≅≡

\begin{code}
module _ {lA}{A : Set lA} where

  infixr 4 _⊚_

  _⊚_ : IsTrans (Id A)
  _⊚_ <> = id

  !_ : IsSym (Id A)
  ! <> = <>

ap₂ : ∀ {lA}{A : ★ lA}{lB}{B : ★ lB}{lC}{C : ★ lC}(f : A → B → C){x w y z} →
      x ≡ y → w ≡ z → f x w ≡ f y z
ap₂ f <> <> = <>

cong₂ = ap₂
\end{code}

TODO J.
TODO Groupoid laws.

## Isomorphisms

\begin{code}
record PseudoIso {lA }(A : Set lA)
                 {l≈A}(_≈A_ : (A → A) → (A → A) → Set l≈A)
                 {lB }(B : Set lB)
                 {l≈B}(_≈B_ : (B → B) → (B → B) → Set l≈B)
                 : Set (lA ⊔ l≈A ⊔ lB ⊔ l≈B) where
  constructor iso
  field to       : A → B
        fr       : B → A
        fr∘to≡id : (fr ∘ to) ≈A id
        to∘fr≡id : (to ∘ fr) ≈B id

infix 1 _≅_

_≅_ : ∀ {lA}(A : Set lA){lB}(B : Set lB) → Set (lA ⊔ lB)
A ≅ B = PseudoIso A _≡_ B _≡_
\end{code}

TODO Define logical equivalence (↔)
TODO Implement ↔ between propositional types → ≅
 
## Dependent product (2)

\begin{code}
Π : ∀ {l1}(A : ★ l1){l2}(B : A → ★ l2) → ★ (l1 ⊔ l2)
Π A B = ∀ a → B a

mapΠ : ∀ {lX lP lQ}{X : ★ lX}{P : X → ★ lP}{Q : X → ★ lQ} →
       (g : ∀ x → P x → Q x) → Π X P → Π X Q
mapΠ = _ˢ_

pamΠ : ∀ {lA lB lY}{A : ★ lA}{B : ★ lB}{Y : A → ★ lY} →
       (f : B → A) → Π A Y → Π B (Y ∘ f)
pamΠ f g = g ∘ f
\end{code}

### Dependent product and equality

\begin{code}
module _ {l1}{X : ★ l1}{l2}{Y : X → ★ l2} where

  infix 4 _Π≡_

  _Π≡_ : (f g : Π X Y) → ★ _
  f Π≡ g = ∀ x → f x ≡ g x

infix 1 _Π≅_

_Π≅_ : ∀ {lA}(A : Set lA){lB}(B : Set lB) → Set (lA ⊔ lB)
A Π≅ B = PseudoIso A _Π≡_ B _Π≡_
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
A Ext l1 , l2 →≅ B = PseudoIso A (λ x y → x Ext l1 , l2 →≡ y)
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

mapΣ : ∀ {lA lB lP lQ}
         {A : ★ lA}{B : ★ lB}{P : A → ★ lP}{Q : B → ★ lQ} →
         (f : A → B)(g : ∀ x → P x → Q (f x)) → Σ A P → Σ B Q
mapΣ f g = Σ.map f (g _)

map× : ∀ {lA lB lC lD}
         {A : ★ lA}{B : ★ lB}{C : ★ lC}{D : ★ lD}
         (f : A → B)(g : C → D) → A × C → B × D
map× f = mapΣ f ∘ κ
\end{code}

### Binary coproduct

\begin{code}
open import Data.Sum public
  using    (_⊎_)
  renaming ( inj₁ to inl ; inj₂ to inr ; map to map⊎ )
module ⊎ = Data.Sum

Two : ∀ {l} → ★ l
Two {l} = ⊤ {l} ⊎ ⊤ {l}

[2] : Set
[2] = Two

pattern «_ x = inl _ , x
pattern »_ x = inr _ , x

module _ {lX}{X : ★ lX}{lY}{Y : ★ lY}{lZ}{Z : (X ⊎ Y) → ★ lZ} where

 «-inj : {a : X}{b : Z (inl a)}{c : Z (inl a)} → 
         Id (Σ (X ⊎ Y) Z) (inl a , b) (inl a , c) → b ≡ c
 «-inj <> = <>

 »-inj : {a : Y}{b : Z (inr a)}{c : Z (inr a)} → 
         Id (Σ (X ⊎ Y) Z) (inr a , b) (inr a , c) → b ≡ c
 »-inj <> = <>
\end{code}

### Dependent coproduct and equality

\begin{code}
module _ {lA}{A : ★ lA}{lB}{B : A → ★ lB} where

  _Σ≡_ : Σ A B → Σ A B → Set _
  (x , y) Σ≡ (z , w) = Σ (x ≡ z) λ p → rew _ p y ≡ w

  Σ≡→≡ : ∀ {p q} → p Σ≡ q → p  ≡ q
  ≡→Σ≡ : ∀ {p q} → p  ≡ q → p Σ≡ q
  Σ≡→≡ (<> , <>) =      <>
  ≡→Σ≡       <>  = <> , <>

  Σ≡≅≡ : ∀ {p q} → p Σ≡ q Π≅ p ≡ q
  Σ≡≅≡ = iso Σ≡→≡ ≡→Σ≡ fr∘to λ _ → uip where
    fr∘to : ∀ {p q} → ≡→Σ≡ ∘ Σ≡→≡ Π≡ id {A = p Σ≡ q}
    fr∘to (<> , <>) = <>
\end{code}

## Pointed sets

\begin{code}
module Pointed l where

  ★∙ = Σ (★ l) id
\end{code}

### Heterogeneous equality

\begin{code}
  _jm≡_ : {A B : ★ l} → A → B → Set
  a jm≡ b = Id ★∙ (, a) (, b)
\end{code}

## Predicates (`Pow`)

Contravariant powerset functor.

TODO. Change notation for Pow everywhere... Maybe ★^ ?

\begin{code}
Pow : ∀ {lX}(X : ★ lX) l → ★ (S l ⊔ lX)
Pow X l = (x : X) → ★ l

Set^  = Pow

infixr 2 _➨_ _⇛_ _⇨_

_⇨_ : ∀ {l1 l2 l3}{I : ★ l1} → Pow I l2 → Pow I l3 → Pow I _
(P ⇨ Q) i = P i → Q i

_➨_ _⇛_ _⇒_ : ∀ {lI lX lY}{I : ★ lI} → Pow I lX → Pow I lY → ★ _
F ➨ G = ∀ {X} → (F ⇨ G) X
X ⇛ Y = Π _ (X ⇨ Y)            
X ⇒ Y = (p : Σ _ X) → Y (fst p) -- <- Hostile to inference: see Functor⇒ below.

module _ {lX lY lP lQ : _}{X : ★ lX}{Y : ★ lY} where

  _pow>_ : Pow X lP → Pow Y lQ → ★ _
  P pow> Q = Σ (X → Y) λ f → P ⇛ Q ∘ f

module ⇛≅⇒ {lI lX lY}{I : ★ lI}(X : Pow I lX)(Y : Pow I lY) where

  to : X ⇛ Y → X ⇒ Y   ; to = uc
  fr : X ⇒ Y → X ⇛ Y   ; fr = cu
  to∘fr : to ∘ fr ≡ id ; to∘fr = <> -- η Σ Π?
  fr∘to : fr ∘ to ≡ id ; fr∘to = <> -- η Σ Π?
\end{code}

### Dependent functions as indexed functions

TODO. A better name for this?

\begin{code}
PowΠ : ∀ {l1 l2}(X : ★ l1) → Pow X l2 → ★ _
PowΠ A B = nκ [1] ⇒ B
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

magic/ : ∀ {l1 l2 l3}{I : ★ l1}{X : Pow I l3} → ⊥/ {l2} ⇛ X
magic/ _ = ⊥-elim

⊤/ : ∀ {l2 l1}{I : ★ l1} → Pow I l2
⊤/ _ = ⊤
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

_×/_ : ∀ {lI}{I : ★ lI}{lX}(X : Pow I lX){lY}(Y : Pow I lY) → I → ★ _
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

## Decidable types

\begin{code}
data Dec? : Set where yes no : Dec?

Dec = λ {l}(X : Set l) → Σ Dec? λ { yes → X ; no  → ¬ X }

module Dec where

  mappam : ∀ {l}{X Y : Set l} → (X → Y) → (Y → X) → Dec X → Dec Y
  mappam f g (yes ,  x) = yes , f x
  mappam f g (no  , ¬x) = no  , ¬x ∘ g
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

  _nt>_ = λ (F G : RawFunctor I O lC lD) → ∀ X → ∣ F ∣ X ⇛ ∣ G ∣ X

  natural : (F G : RawFunctor I O lC lD) → F nt> G → ★ _
  natural F G α = ∀ {A B}(f : A ⇛ B) → α B ∘⇛ ∣ F ∣map f Π≡ ∣ G ∣map f ∘⇛ α A

  record _NT>_ (F : RawFunctor I O lC lD)(G : RawFunctor I O lC lD) : ★ (lD ⊔ S lC ⊔ lI) where
    field
      _<$>_ : F nt> G
      isNat : natural F G _<$>_
\end{code}

TODO. Is the naming correct? Check Hancock's thesis.

## Families (`Fam`)

We keep it as small as `A` thanks to the small identity type.

\begin{code}
_⁻¹_ : ∀ {lA lB}{A : ★ lA}{B : ★ lB} → (A → B) → Pow B lA -- (lA ⊔ lB)
f ⁻¹ b = Σ _ λ a → f a ≡ b  -- lB does not count (anymore)!
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
module _ where

  open Functor

  ■ : ∀ {lX lI}{O N : ★ lI}(F : Functor O N lX lX) →
      ∀ {X} → Pow/ X lX → Pow/ (∣ F ∣ X) lX
  ■ F = fromFam/ ∘ ,_ ∘ ∣ F ∣map ∘ snd ∘ toFam/

  all■ : ∀ {lX lI : _}{O N : ★ lI}(F : Functor O N lX lX)
         {X : Pow O lX}{P : Pow/ X lX} → Π _ P → Π _ (■ F P)
  all■ F m (n , xs) = ∣ F ∣map (λ o x → x , m (o , x)) n xs
                    , (∣ F ∣map-∘⇛ (n , xs) ⊚ ∣ F ∣map-id⇛ (n , xs))
\end{code}

### Families as containers

\begin{code}
Cont = λ lI l → Fam (Set l {- ^op -}) lI

⟦_⟧Cont : ∀ {l lX} → Cont l lX → Set lX → Set (l ⊔ lX)
⟦ S , P ⟧Cont X = Σ S λ s → P s → X
\end{code}

## Abstract nonsense

\begin{code}
module ANS {lO}{O : Set lO}{lN}{N : Set lN}(f : O → N){l} where

  ΔF : Pow N l → Pow O l
  ΔF X o = X (f o)

  ΣF ΠF : Pow O l → Pow N (l ⊔ lO)
  ΣF X n = Σ (f ⁻¹ n) (X ∘ fst)
  ΠF X n = Π (f ⁻¹ n) (X ∘ fst)
\end{code}

\begin{code}
  pam : Fam N l → Fam O (l ⊔ lO)
  pam (X , k) = Σ X (_⁻¹_ f ∘ k) , fst ∘ snd

  map : Fam O l → Fam N l
  map (X , k) = X , f ∘ k
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

Why do we use lists instead of starting out with natural numbers and
base the development on normal functors?

The main reason is that we will use lists often and we want to avoid
the encoding overhead for them.

### Contexts

We can already describe left-nested (nameless) records,
i.e. higher-order codes for first-order dependently-typed lists.

(The mutual definition is not necessary but it is nicer).

\begin{code}
module Cx {lU}{U : Set lU}{lEl}(El : Pow U lEl) where

  Cx    :          Pow (List U) (lEl ⊔ lU)
  ⟦_⟧Cx : ∀ {xs} → Pow (Cx xs ) (lEl ⊔ lU)

  Cx (    []) = ⊤
  Cx (x ∷ xs) = Σ (Cx xs) λ xs → ⟦ xs ⟧Cx → U
  ⟦_⟧Cx {[]}         _  = ⊤
  ⟦_⟧Cx {_ ∷ _} (Γ , τ) = Σ ⟦ Γ ⟧Cx λ s → El (τ s)
\end{code}

### □List

As we do not usually need so many dependencies we can obtain a
(smaller) first-order cons-list by induction.

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
           (∀ x xs p ps → C (xs , ps) → C (x ∷ xs , p , ps)) →
           ∀ x → C x
    elim m[] m∷ ([]     ,      _) = m[]
    elim m[] m∷ (x ∷ xs , p , ps) = m∷ _ _ _ _ (elim m[] m∷ (xs , ps))
\end{code}

Star is often useful.

TODO. Prove it isomorphic to the one from the standard library.

\begin{code}
module _ {lA lR : Level}{A : ★ lA} where

  chain : A → A → List A → List (A × A)
  chain b e []       = (b , e) ∷ []
  chain b e (x ∷ xs) = (b , x) ∷ chain x e xs

  _[_]✰_ : A → (A → Pow A lR) → A → Set _
  x [ R ]✰ y = Σ (List A) (□List (uc R) ∘ chain x y)
\end{code}

## Natural numbers

We could now use lists as natural numbers.

\begin{code}
module ℕ=List⊤ where

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
numbers (for example, the bidirectional elaboration of numerals), so
we resort to importing `Data.Nat`.

\begin{code}
open import Data.Nat public using (ℕ ; zero ; suc ; _+_ ; _*_)
module ℕ = Data.Nat

private example : 3 * 2 ≡ 6 ; example = <>
\end{code}

Vectors.

\begin{code}
toList : ℕ → ℕ=List⊤.ℕ
toList zero    = ℕ=List⊤.zero
toList (suc n) = ℕ=List⊤.suc (toList n)

Vec = λ {l}(X : Set l) → □List (λ _ → X) ∘ toList
\end{code}

TODO Move somewhere else.

Normal functor codes and their semantics.

\begin{code}
Normal : ∀ lA → Set _
Normal lA = Σ (Set lA) λ A → A → ℕ

⟦_⟧N : ∀ {lA} → Normal lA → ∀ {l} → Set l → Set (l ⊔ lA)
⟦ A , ∣_∣ ⟧N X = Σ A (Vec X ∘ ∣_∣)

-- TODO Fin is in Ix
module Normal (Fin : ∀ {l} → ℕ → Set l) where

  toCont : ∀ {l} → Normal l → Cont l (S l)
  toCont (A , ∣_∣) = A , Fin ∘ ∣_∣
\end{code}

## At-key

\begin{code}
module _ {lI}{I : ★ lI} where

  [_:=_] : Pow I lI → I → Pow I lI
  [ X := i ] = ≡ i ×/ X

  [κ_:=_] : Set lI → I → Pow I lI
  [κ_:=_] X i = [ (λ (i : _) → X) := i ]
\end{code}

## Sorry

\begin{code}
module _ {l} where

  open Pointed l

  _!!!_Ty : List ★∙ → ℕ → Set _
  []       !!! n     Ty = ⊤
  (x ∷ xs) !!! zero  Ty = fst x
  (x ∷ xs) !!! suc n Ty = xs !!! n Ty

  _!!!_ : (xs : List ★∙) → (i : ℕ) → xs !!! i Ty
  []       !!! i     = tt
  (x ∷ xs) !!! zero  = snd x
  (x ∷ xs) !!! suc i = xs !!! i
\end{code}

\begin{code}
  module 1Point (points : List ★∙)(offset : ℕ) where
    #0 = points !!! offset

  module 2Points (points : List ★∙)(offset : ℕ) where
    open 1Point points (      offset) public
    open 1Point points (1 ℕ.+ offset) public renaming (#0 to #1)

  module 4Points (points : List ★∙)(offset : ℕ) where
    open 2Points points (      offset) public
    open 2Points points (2 ℕ.+ offset) public
      renaming (#0 to #2 ; #1 to #3)

  module 8Points (points : List ★∙)(offset : ℕ) where
    open 4Points points (      offset) public
    open 4Points points (4 ℕ.+ offset) public
      renaming (#0 to #4 ; #1 to #5 ; #2 to #6 ; #3 to #7)

  module 16Points (points : List ★∙)(offset : ℕ) where
    open 8Points points (      offset) public
    open 8Points points (8 ℕ.+ offset) public
      renaming (#0 to #8  ; #1 to #9  ; #2 to #10 ; #3 to #11
               ;#4 to #12 ; #5 to #13 ; #6 to #14 ; #7 to #15)

  module 32Points (points : List ★∙)(offset : ℕ) where
    open 16Points points (       offset) public
    open 16Points points (16 ℕ.+ offset) public
      renaming (#0  to #16 ; #1  to #17 ; #2  to #18 ; #3  to #19
               ;#4  to #20 ; #5  to #21 ; #6  to #22 ; #7  to #23
               ;#8  to #24 ; #9  to #25 ; #10 to #26 ; #11 to #27
               ;#12 to #28 ; #13 to #29 ; #14 to #30 ; #15 to #31)
\end{code}
