import R1UnifiedLabels
import R1SelectedTranscriptParams

/-! Aspis one-transaction verifier: the row labels and the challenge map for
the 40-row transcript (R1 rows 0 to 32, then the combining challenge, row 33,
and six round challenges, rows 34 to 39).

R1's definitions `UnifiedLabels.label`, `UnifiedLabels.row`,
`SelectedTranscriptParams.label` and `SelectedChallengeMap.sigma` are already
defined for every row number; only their lemmas carry the bound `n < 33`.
This file restates those lemmas for `n < 40`, over the SAME definitions, and
records that the challenge map of rows 32 to 39 is the qm31 sampler
`R0P.SemSource.semChal` (Rust `Transcript::scalar_k`, transcript.rs line 36).
Nothing here is a Rust refinement beyond the label byte `0xa0 + n`. -/
set_option autoImplicit false
noncomputable section
namespace AspisRows40.Labels

open AspisV8R19.DuplexFrames
open AspisR1

/-- Number of rows of the Aspis transcript. -/
def rowCount : Nat := 40

theorem label_val (n : Nat) (hn : n < 40) : (UnifiedLabels.label n).val = 160 + n := by
  simp only [UnifiedLabels.label, Fin.val_mk]
  rw [Nat.mod_eq_of_lt]
  omega

theorem label_injective {i j : Nat} (hi : i < 40) (hj : j < 40)
    (h : UnifiedLabels.label i = UnifiedLabels.label j) : i = j := by
  have hv := congrArg Fin.val h
  rw [label_val i hi, label_val j hj] at hv
  omega

theorem row_label (n : Nat) (hn : n < 40) : UnifiedLabels.row (UnifiedLabels.label n) = n := by
  simp [UnifiedLabels.row, label_val n hn]

/-- The 40-row lemma agrees with R1's on R1's rows (same definitions). -/
theorem row_label_r1 (n : Nat) (hn : n < 33) :
    row_label n (by omega) = UnifiedLabels.row_label n hn := rfl

/-- The label bytes of the seven new rows are 0xc1 .. 0xc7 (193 .. 199). -/
theorem label_final_val (n : Nat) (hlo : 33 ≤ n) (hhi : n < 40) :
    193 ≤ (UnifiedLabels.label n).val ∧ (UnifiedLabels.label n).val ≤ 199 := by
  rw [label_val n hhi]; omega

/-- No new label equals an R1 label. -/
theorem label_ne_r1 {i j : Nat} (hi : i < 33) (hlo : 33 ≤ j) (hj : j < 40) :
    UnifiedLabels.label i ≠ UnifiedLabels.label j := by
  intro h
  have := label_injective (by omega : i < 40) hj h
  omega

/-- The selected protocol parameters use the same label function. -/
theorem params_lbl (n : Nat) :
    SelectedTranscriptParams.params.lbl n = UnifiedLabels.label n := rfl

/-- The challenge map of rows 32 to 39 is the qm31 sampler embedded in the
wide field. R1 uses this branch for row 32 (rho); the Rust verifier draws rows
33 to 39 with the same function `Transcript::scalar_k` as row 32. -/
theorem sigma_qm31 (i : Nat) (h32 : 32 ≤ i) (s : AspisV8R19.SourceDuplexStep.State) :
    SelectedTranscriptParams.params.σ i s = R0P.SemSource.semChal s := by
  change SelectedChallengeMap.sigma i s = _
  have h27 : i ≠ 27 := by omega
  have hopen : ¬ (i = 28 ∨ i = 29 ∨ i = 30) := by omega
  have h31 : i ≠ 31 := by omega
  simp only [SelectedChallengeMap.sigma, if_neg h27, if_neg hopen, if_neg h31]

/-- The new rows' challenge equals row 32's challenge map, pointwise. -/
theorem sigma_final_eq_rho (i : Nat) (hlo : 33 ≤ i) (s : AspisV8R19.SourceDuplexStep.State) :
    SelectedTranscriptParams.params.σ i s = SelectedTranscriptParams.params.σ 32 s := by
  rw [sigma_qm31 i (by omega), sigma_qm31 32 le_rfl]

#print axioms label_val
#print axioms label_injective
#print axioms row_label
#print axioms row_label_r1
#print axioms label_final_val
#print axioms label_ne_r1
#print axioms params_lbl
#print axioms sigma_qm31
#print axioms sigma_final_eq_rho

end AspisRows40.Labels
end
