import R1Z.QueryScanHistorySplit

/-! A fixed-event execution join cannot follow from builder facts alone
while the source experiment remains arbitrary. This is a typed obstruction
to deleting the release's execution premise without a concrete source law. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.BuilderExecutionBoundary
open R0Z R0Z.FsStatement R0Z.FsAbort R1Z.QueryScanHistorySplit
attribute [local instance] Classical.propDecidable

theorem constant_mismatch_forces_full_bad
    {R M : Type} [Fintype R] [Fintype M]
    (bad : Fin 8 → M → Prop)
    (e : ModelExecutionJoin (fun _ : R => (0 : ℚ)) (fun _ : M => (1 : ℚ)) bad) :
    eventMass (fun m => ∃ i, bad i m) = 1 := by
  have hall : ∀ s : e.cp.S, ∃ i, bad i (e.cp.toM s) := by
    intro s
    by_contra hn
    have h := e.agreement s hn
    norm_num at h
  have ht := e.cp.meanM (fun m : M => @ite ℚ (∃ i, bad i m) (Classical.propDecidable _) 1 0)
  simp only [hall,if_true,mean_const] at ht
  simpa [eventMass] using ht.symm

theorem no_constant_mismatch_join
    {R M : Type} [Fintype R] [Fintype M]
    (bad : Fin 8 → M → Prop)
    (hsmall : eventMass (fun m => ∃ i, bad i m) < 1) :
    ¬ Nonempty (ModelExecutionJoin (fun _ : R => (0 : ℚ)) (fun _ : M => (1 : ℚ)) bad) := by
  rintro ⟨e⟩
  rw [constant_mismatch_forces_full_bad bad e] at hsmall
  exact (lt_irrefl (1 : ℚ)) hsmall

#print axioms constant_mismatch_forces_full_bad
#print axioms no_constant_mismatch_join
end R1Z.BuilderExecutionBoundary
