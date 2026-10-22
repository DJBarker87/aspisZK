import R1Z.ProverCommitPublicPrefix41

/-! Agreement half of conditional programming. Public reads are coherent
memo reads, not fresh coins. Repeated private reads may also be retained
provided their answers agree. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitMixedReads41
open R0Z R0Z.FsStatement R1Z.LazyFrozen R1Z.LazyTable
attribute [local instance] Classical.propDecidable
variable {A U : Type} [DecidableEq A]

/-- Public memo reads are answered by the original table; every non-frozen
first occurrence is answered by its own lazy coordinate. Later occurrences
reuse that first answer. -/
theorem coherent_answers (Fr : Finset A) {m : Nat}
    (a : Fin m → (Fin m → U) → (A → U) → A)
    (table : A → U) (coins : Fin m → U)
    (memo : ∀ i, a i coins table ∈ Fr → coins i = table (a i coins table))
    (repeats : ∀ i j, a i coins table = a j coins table → coins i = coins j)
    (i : Fin m) :
    progF Fr a table coins (a i coins table) = coins i := by
  by_cases hf : a i coins table ∈ Fr
  · exact (progF_frozen Fr a table coins _ hf).trans (memo i hf).symm
  · let seen : Finset (Fin m) := Finset.univ.filter (fun j => a j coins table = a i coins table)
    have nonempty : seen.Nonempty := ⟨i,by simp [seen]⟩
    let j := seen.min' nonempty
    have hj : a j coins table = a i coins table :=
      (Finset.mem_filter.mp (Finset.min'_mem seen nonempty)).2
    have first : ∀ k, k < j → a k coins table ≠ a j coins table := by
      intro k hk same
      have member : k ∈ seen := by simp only [seen,Finset.mem_filter,Finset.mem_univ,true_and]; exact same.trans hj
      exact (not_le_of_gt hk) (Finset.min'_le seen k member)
    rw [← hj]
    exact (progF_first Fr a table coins j (fun h => hf (hj ▸ h)) first).trans
      (repeats j i hj)

/-- Mixed public/private agreement replaces run_eqF's false requirement that
all reads be outside the frozen prefix. It also preserves repeated reads. -/
theorem run_eq_mixed (Fr : Finset A) {m : Nat}
    (a : Fin m → (Fin m → U) → (A → U) → A) (causal : CausalF Fr a)
    (table : A → U) (coins actual : Fin m → U)
    (memo : ∀ i, a i coins table ∈ Fr → coins i = table (a i coins table))
    (repeats : ∀ i j, a i coins table = a j coins table → coins i = coins j)
    (run : ∀ i, actual i = progF Fr a table coins
      (a i actual (progF Fr a table coins))) : actual = coins := by
  have frozen : ∀ y ∈ Fr, progF Fr a table coins y = table y :=
    fun y hy => progF_frozen Fr a table coins y hy
  apply run_unique (fun i v => a i v table)
    (fun i v v' h => causal i v v' table table h (fun _ _ => rfl))
    (progF Fr a table coins) actual coins
  · intro i
    rw [run i,causal i actual actual _ table (fun _ _ => rfl) frozen]
  · intro i
    exact (coherent_answers Fr a table coins memo repeats i).symm

/-- Conditional law and mixed agreement are separate obligations: first-hit
coherence does not follow from fresh marginal coins at public positions. -/
theorem first_memo (Fr : Finset A) {m : Nat}
    (a : Fin m → (Fin m → U) → (A → U) → A)
    (table : A → U) (coins : Fin m → U) (i : Fin m)
    (hit : a i coins table ∈ Fr) :
    progF Fr a table coins (a i coins table) = table (a i coins table) :=
  progF_frozen Fr a table coins _ hit

#print axioms coherent_answers
#print axioms run_eq_mixed
#print axioms first_memo
end R1Z.ProverCommitMixedReads41
