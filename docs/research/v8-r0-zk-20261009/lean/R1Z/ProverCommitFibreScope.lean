import R1Z.GamesR1PBin

/-! The full ideal tape retains redundant H1 coordinates. A source adapter
which zero-fills one such coordinate cannot have equal successful fibres.
This rules out that adapter, not every possible randomized completion. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitFibreScope
open R0Z.JointView R0Z.MaskLayout
attribute [local instance] Classical.propDecidable

/-- H1 lane 1, dependent row 0, limb 0. The model carries this raw coordinate
although balance overwrites its value and Rust does not sample it. -/
def ignoredH1 : AffCoordinate := .inr (1, 0, 0)

theorem zero_fill_not_equal_fibres
    {Input K : Type} [Fintype Input] [Field K] [Fintype K]
    (F : Subfield K) (decode : Input → Option (Tape K F))
    (forced : ∀ input tape, decode input = some tape → tape.1 ignoredH1 = 0)
    (input : Input) (tape : Tape K F) (success : decode input = some tape) :
    ¬ ∃ cF : ℕ, ∀ τ : Tape K F,
      (Finset.univ.filter (fun e : Input => decode e = some τ)).card = cF := by
  classical
  rintro ⟨cF, equal⟩
  let missing : Tape K F := ((fun _ => 1), (fun _ => 0))
  have absent : ∀ e, decode e ≠ some missing := by
    intro e h
    have bad := forced e missing h
    exact one_ne_zero (by simpa only [missing] using bad)
  have empty : (Finset.univ.filter (fun e : Input => decode e = some missing)) = ∅ := by
    ext e
    simp [absent e]
  have zero : cF = 0 := by
    have h := equal missing
    rw [empty, Finset.card_empty] at h
    exact h.symm
  have positive : 0 < (Finset.univ.filter (fun e : Input => decode e = some tape)).card := by
    apply Finset.card_pos.mpr
    exact ⟨input, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact success⟩
  rw [equal tape, zero] at positive
  exact (Nat.lt_irrefl 0) positive

#print axioms zero_fill_not_equal_fibres
end R1Z.ProverCommitFibreScope
