[2014 Matteo Acerbi](https://www.gnu.org/licenses/gpl.html)

# A type for assignments

Assume we have a family of types `A` for agents, indexed by the list
of tasks of type `T` they are assigned to.

\begin{code}
open import AD

module Assignment {lT}{T : Set lT}{lA}(A : List T → Set lA) where
\end{code}

For example `a` is an agent which must carry out tasks `t1` and t2`.

    a : A (t1 ∷ t2 ∷ [])

We want to define a family of **assignments** indexed by a lists of
tasks, under the constraint that exactly one agent is assigned to each
of the tasks.

We can model assignments as a dependent tuple composed of the number
of agents, a finite map from tasks to agent identifiers, and the
agent's data for any agent identifier.

\begin{code}
open Ix Z

Indices : List T → ℕ → Set
Indices xs n = □List (nκ (Fin n)) xs
\end{code}

A possible solution: for any `j : Fin n` where `n` is the number of
agents, search all occurrences of `j` in `is` and ask for an agent for
the returned list of tasks.

\begin{code}
module Alt where

  getTasks : ∀ {xs : List T}{n} → □List (nκ (Fin n)) xs → Fin n → List T
  getTasks {[]    } is       j = []
  getTasks {x ∷ xs} (i , is) j with i ≟ j
  getTasks {x ∷ xs} (i , is) j | yes , _ = x ∷ getTasks is j
  getTasks {x ∷ xs} (i , is) j | no  , _ = getTasks is j

  Agents : ∀ {ts n} → (is : Indices ts n) → Set lA
  Agents is = ∀ j → A (getTasks is j)
\end{code}

We prefer the following first-order alternative.

From the vector of indices we obtain a vector of lists of tasks by
placing, for each index `i` in the list, the resource at the same
position in the bucket located by `i`.

\begin{code}
assign : ∀ {ts} n → Indices ts n → Vec (List T) n
assign n = □List.elim (m[] _) (λ r _ i _ tss → m∷ r _ i tss) ∘ _,_ _ where
  m[] : ∀ n → Vec (List T) n
  m[] zero    = _
  m[] (suc n) = [] , m[] n
  m∷ : ∀ r n → Fin n → Vec (List T) n → Vec (List T) n
  m∷ r zero    ()
  m∷ r (suc n) (|1  ) (ts , tss) = r ∷ ts , tss
  m∷ r (suc n) (|0 i) (ts , tss) =     ts , m∷ r n i tss

module _ (t1 t2 t3 t4 : T) where

  ts = t1 ∷ t2 ∷ t3 ∷ t4 ∷ []

  test :   assign {ts = ts} 5 (|0 |1 , |0 |0 |0 |1 , |1 , |0 |1 , tt)
        ≡ ( t3 ∷ []
          , t1 ∷ t4 ∷ []
          , []
          , t2 ∷ []
          , _)
  test = <>
\end{code}

`Agents n is` is a type of `n` agents for the tasks corresponding to
the indices in `is`.

\begin{code}
Agents : ∀ {ts} n → (is : Indices ts n) → Set lA
Agents n is = □List.elim ⊤ (λ _ _ ts tss X → A ts × X)
                           (_ , assign n is)
\end{code}

`Assignment/ ts n` is the type of the assignments to `n` agents of the
tasks in `ts`.

\begin{code}
Assignment/ : List T → ℕ → Set _
Assignment/ xs n = Σ (Indices xs n) (Agents n)
\end{code}

The family we were after should therefore be the following, where we
"abstract" from the number of agents.

\begin{code}
Assignment : List T → Set _
Assignment = Σ _ ∘ Assignment/
\end{code}

## Tests

\begin{code}
module SimpleTransfer (send : ∀ {ts} → (i : Ix ts) → A ts    → A (− i))
                      (recv : ∀ {ts} → (i : Ix ts) → A (− i) → A ts   )
                      where

  swap2 : ∀ {t} → Assignment/ (t ∷ []) 2 → Assignment/ (t ∷ []) 2
  -- a1 is assigned the task, we reassign it to a2
  swap2 ((|1       , _) , a1 , a2 , _) = (|0 |1 , _) , send |1 a1 , recv |1 a2 , _
  -- a2 is assigned the task, we reassign it to a1
  swap2 ((|0 |1    , _) , a1 , a2 , _) = (|1    , _) , recv |1 a1 , send |1 a2 , _
  -- there are no more possibilities
  swap2 ((|0 |0 () , _) , a1 , a2 , _)
\end{code}

* TODO The above is "wrong".

Or, at least, it does not really correspond to the description.

(Fortunately) lists are not finite sets ("buckets").

Here an `Assignment (t1 ∷ t2 ∷ ts)` has no way to contain an agent of type `A (t2 ∷ t1 ∷ [])`.

It makes sense when ∀ xs (p : Permutation xs) → A xs ≅ A ⟦ p ⟧, but I did not assume this.

* TODO Prior art? Better alternatives?
