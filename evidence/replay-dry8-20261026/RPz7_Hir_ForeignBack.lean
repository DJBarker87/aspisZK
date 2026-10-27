import RPz7_Hir_Zero
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_ForeignBack
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call Hir_Schedule Hir_ProvenanceModel

theorem unchanged {A : Type}
    (native1 : S2W_ExtractionBoundary.First)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (store : Store)
    (caller : S2W_ExtractionBoundary.Program) (address key : Nat) (value : Cell)
    (allowed : (Hiq_NativeAction.apply native1 copy allocator id store (.foreign caller address value)).2 = .rollback ∨
      Assignable store address value)
    (owner : ((Hiq_NativeAction.apply native1 copy allocator id store (.foreign caller address value)).1 key).owner = id)
    (marker : Initialized ((Hiq_NativeAction.apply native1 copy allocator id store (.foreign caller address value)).1 key).data) :
    (Hiq_NativeAction.apply native1 copy allocator id store (.foreign caller address value)).1 key = store key := by
  classical
  by_cases authorized : caller ≠ id ∧ (store address).owner = caller
  · simp only [Hiq_NativeAction.apply,if_pos authorized] at allowed owner marker ⊢
    by_cases same : key = address
    · subst key
      rw [put_here] at owner marker ⊢
      rcases allowed with impossible | assign
      · cases impossible
      · rcases assign with old | zero
        · exact False.elim (authorized.1 (authorized.2.symm.trans (old.symm.trans owner)))
        · exact False.elim (Hir_Zero.not_initialized value.data zero marker)
    · exact put_other store address key value same
  · simp only [Hiq_NativeAction.apply,if_neg authorized]

#print axioms unchanged
end AspisR1.Hir_ForeignBack
end
