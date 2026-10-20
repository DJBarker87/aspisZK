import R1Z.CommitReadsR1
set_option autoImplicit false
namespace R1Z.ProverCommitExhaustionScope
open R1Z.CommitReadsR1 R0Z.FsAbortBounds

/-- A successful prefix may be followed by a rejection window in unused
padded words. The carrier has all 16(cut+1) words required by the model
capacity bound. This separates actual consumption from a worst-case budget. -/
def paddedWords (cut : ℕ) : Fin (16 * (cut + 1)) → Word := fun i =>
  if i.val < cut then 0 else ⟨2147483647, by norm_num⟩

theorem accepted_prefix (cut l : ℕ) (hl : l ≤ cut) :
    limbPos (paddedWords cut) l = some l := by
  induction l with
  | zero => rfl
  | succ l ih =>
    rw [limbPos, ih (by omega)]
    simp [tryLimb, getW, paddedWords, show l < cut by omega,
      show l < 16 * (cut + 1) by omega, rejB, P31]

theorem rejected_suffix (cut r p : ℕ) (hp : cut ≤ p) (hr : p + r ≤ cut + 16) :
    tryLimb (paddedWords cut) p r = none := by
  induction r generalizing p with
  | zero => rfl
  | succ r ih =>
    rw [tryLimb]
    have hrej : rejB (getW (paddedWords cut) p) = true := by
      simp [getW, paddedWords, show p < 16 * (cut + 1) by omega,
        show ¬ p < cut by omega, rejB, P31]
    rw [hrej]
    exact ih (p+1) (by omega) (by omega)

theorem exhausted_succ (cut : ℕ) : Exhausted (paddedWords cut) (cut+1) := by
  change limbPos (paddedWords cut) (cut+1) = none
  rw [limbPos, accepted_prefix cut cut (by omega)]
  exact rejected_suffix cut 16 cut (by omega) (by omega)

theorem padded_converse_false (cut : ℕ) :
    limbPos (paddedWords cut) cut = some cut ∧
      Exhausted (paddedWords cut) (cut+1) :=
  ⟨accepted_prefix cut cut (by omega), exhausted_succ cut⟩

/-- A concrete worst-budget word stream: a much shorter prefix decodes,
but decoding the padded 45056-limb budget exhausts. This is a model
counterexample, not an asserted Rust tapeOf instance. -/
theorem worst_budget_counterexample :
    ∃ ws : Fin (90112 * 8) → Word,
      limbPos ws 21375 = some 21375 ∧ Exhausted ws 45056 := by
  refine ⟨paddedWords 45055, ?_, ?_⟩
  · exact accepted_prefix 45055 21375 (by omega)
  · exact exhausted_succ 45055

#print axioms worst_budget_counterexample
#print axioms accepted_prefix
#print axioms rejected_suffix
#print axioms exhausted_succ
#print axioms padded_converse_false
end R1Z.ProverCommitExhaustionScope
