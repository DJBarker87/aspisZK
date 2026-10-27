import PV_B1_Close258
set_option autoImplicit false
noncomputable section
namespace PV_B1_PoleWitnesses
open Aeneas Aeneas.Std Result ProverRwFull PV_B1_Transport PV_B1_ActualInstall
variable [ExternalTypes]
theorem nonempty (ops : ExternalFuns) (m : Array U16 64#usize) (c : HQ)
    (r : Array (Array HQ 2#usize) 2#usize) :
    ∃ b, (selected ops).op258 (⟨[r],by simp only [List.length_cons,List.length_nil]; scalar_tac⟩ : Rows) m c=ok b := by
  apply PV_B1_PoleOutcome.total
  change 1≤1024
  omega

theorem failure_nonvacuity (ops : ExternalFuns) (m : Array U16 64#usize) (c : HQ)
    (r : Array (Array HQ 2#usize) 2#usize) :
    (selected ops).op258 (⟨List.replicate 1025 r,by simp only [List.length_replicate]; scalar_tac⟩ : Rows) m c=
      fail .arrayOutOfBounds := by
  apply (PV_B1_Close258.failure ops _ m c).mpr
  simp only [List.length_replicate]
  omega

theorem falsity (ops : ExternalFuns) (v : Rows) (m : Array U16 64#usize) (c : HQ) :
    (selected ops).op258 v m c=ok false ↔ (rows v).val.length≤1024 ∧
      ¬ (∀ i : Nat, i<(rows v).val.length → PV_B1_Orig258_Op258Fold.keep (rows v) m
        (PV_B1_ActualCarrier258.toQ c) (PV_B1_Orig258_PoleAdvance.advance i 0#usize)=true) :=
  PV_B1_PoleFalseLaw.false_iff _ _ _
#print axioms nonempty
#print axioms failure_nonvacuity
#print axioms falsity
end PV_B1_PoleWitnesses
