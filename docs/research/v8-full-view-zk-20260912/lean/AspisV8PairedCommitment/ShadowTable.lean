import AspisV8PairedCommitment.Table

/-!
Operational fragment of the forward eager/delayed relation. `hidden` is
proof-side bookkeeping, not observer input. A probability theorem must prove
the coupling's two marginals in addition to these deterministic transitions.
-/
namespace AspisV8PairedCommitment

variable {Input Answer : Type*} [DecidableEq Input] [DecidableEq Answer]

/-- A real lazy-oracle call reuses cached answers, even on a bad execution. -/
def queryStep (table : Table Input Answer) (input : Input) (fresh : Answer) :
    Answer × Table Input Answer :=
  match table input with
  | some old => (old, table)
  | none => (fresh, put table input fresh)

/-- The private eager table may contain extra, still-deferred leaf entries. -/
def AgreeExcept (hidden : Input → Prop) (eager delayed : Table Input Answer) : Prop :=
  ∀ input, ¬ hidden input → eager input = delayed input

theorem cached_query_reuses_answer (table : Table Input Answer) (input : Input)
    (old fresh : Answer) (cached : table input = some old) :
    queryStep table input fresh = (old, table) := by
  simp [queryStep, cached]

/-- Outside deferred inputs, ordinary queries preserve the actual relation. -/
theorem ordinary_query_agrees
    (hidden : Input → Prop) (eager delayed : Table Input Answer)
    (input : Input) (fresh : Answer)
    (agree : AgreeExcept hidden eager delayed) (outside : ¬ hidden input) :
    (queryStep eager input fresh).1 = (queryStep delayed input fresh).1 ∧
    AgreeExcept hidden (queryStep eager input fresh).2 (queryStep delayed input fresh).2 := by
  have same := agree input outside
  unfold queryStep
  rw [same]
  cases found : delayed input with
  | none =>
      constructor
      · rfl
      · intro query hquery
        by_cases eqInput : query = input
        · subst query
          simp [put]
        · simpa [put, eqInput] using agree query hquery
  | some answer =>
      exact ⟨rfl, agree⟩

/-- A pair installation touches no other input, whether it succeeds or fails. -/
theorem pair_install_other_lookup (table : Table Input Answer)
    (i j query : Input) (a b : Answer)
    (notI : query ≠ i) (notJ : query ≠ j) :
    (installPair table i j a b).1 query = table query := by
  by_cases safe : i ≠ j ∧ Fits table i a ∧ Fits table j b
  · simp [installPair, safe, put, notI, notJ]
  · simp [installPair, safe]

/-- Materialising both paired entries removes them from the deferred set. -/
theorem paired_materialization_shrinks_hidden
    (hidden : Input → Prop) (eager delayed : Table Input Answer)
    (i j : Input) (a b : Answer)
    (agree : AgreeExcept hidden eager delayed)
    (eagerI : eager i = some a) (eagerJ : eager j = some b)
    (success : (installPair delayed i j a b).2 = true) :
    AgreeExcept (fun query => hidden query ∧ query ≠ i ∧ query ≠ j)
      eager (installPair delayed i j a b).1 := by
  obtain ⟨_, installedI, installedJ⟩ := accepted_pair_is_safe delayed i j a b success
  intro query outside
  by_cases isI : query = i
  · subst query
    exact eagerI.trans installedI.symm
  by_cases isJ : query = j
  · subst query
    exact eagerJ.trans installedJ.symm
  have notHidden : ¬ hidden query := by
    intro isHidden
    exact outside ⟨isHidden, isI, isJ⟩
  calc
    eager query = delayed query := agree query notHidden
    _ = (installPair delayed i j a b).1 query :=
      (pair_install_other_lookup delayed i j query a b isI isJ).symm

#print axioms cached_query_reuses_answer
#print axioms ordinary_query_agrees
#print axioms paired_materialization_shrinks_hidden
end AspisV8PairedCommitment
