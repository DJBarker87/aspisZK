import PV_B1_ActualInstall
import PV_B1_PoleOutcome
import PV_B1_PoleFalseLaw
import PV_B1_PoleControl
set_option autoImplicit false
noncomputable section
namespace PV_B1_258
open Aeneas Aeneas.Std Result
theorem source (v : Slice (Array (Array aspis_core.field.QM31 2#usize) 2#usize))
    (m : Array U16 64#usize) (c : aspis_core.field.QM31) :
    all_slots_clear v m c=PV_B1_PoleOriginal.reference.all_slots_clear v m c :=
  PV_B1_PoleBridge.op258_source v m c
#print axioms source
end PV_B1_258
namespace PV_B1_Close258
open Aeneas Aeneas.Std Result ProverRwFull PV_B1_Transport PV_B1_ActualInstall
variable [ExternalTypes]
theorem selected_callback (ops : ExternalFuns) (v : Rows) (m : Array U16 64#usize) (c : HQ) :
    (selected ops).op258 v m c=
      PV_B1_PoleOriginal.reference.all_slots_clear (rows v) m (PV_B1_ActualCarrier258.toQ c) :=
  op258_source ops v m c

theorem truth (ops : ExternalFuns) (v : Rows) (m : Array U16 64#usize) (c : HQ) :
    (selected ops).op258 v m c=ok true ↔ (rows v).val.length≤1024 ∧
      ∀ i : Nat, i<(rows v).val.length → PV_B1_Orig258_Op258Fold.keep (rows v) m
        (PV_B1_ActualCarrier258.toQ c) (PV_B1_Orig258_PoleAdvance.advance i 0#usize)=true :=
  PV_B1_PoleOutcome.truth_iff _ _ _

theorem failure (ops : ExternalFuns) (v : Rows) (m : Array U16 64#usize) (c : HQ) :
    (selected ops).op258 v m c=fail .arrayOutOfBounds ↔ 1024<v.val.length := by
  change PV_B1_258.all_slots_clear _ _ _=_ ↔ _
  rw [PV_B1_PoleOutcome.failure_iff]
  change 1024<(v.val.map _).length ↔ _
  rw [List.length_map]

theorem nonvacuity (ops : ExternalFuns) (m : Array U16 64#usize) (c : HQ) :
    (selected ops).op258 (⟨[],by decide⟩ : Rows) m c=ok true := by
  apply (truth ops _ m c).mpr
  constructor
  · change 0≤1024; omega
  · intro i h; change i<0 at h; omega
#print axioms selected_callback
#print axioms truth
#print axioms failure
#print axioms nonvacuity
end PV_B1_Close258
