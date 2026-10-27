import PV_B1_HostPoleOutcome
import PV_B1_PoleFalseLaw
set_option autoImplicit false
noncomputable section
namespace PV_B1_HostPoleTruth
open Aeneas Aeneas.Std Result PV_B1_Transport
open PV_B1_Host PV_B1_Install
variable [ExternalTypes]
theorem truth (ops : ExternalFuns) (v : Rows) (m : Array U16 64#usize) (c : HQ) :
    (selected ops).op258 v m c=ok true ↔ v.val.length≤1024 ∧
      ∀ i : Nat, i<v.val.length → PV_B1_Orig258_Op258Fold.keep (rows v) m
        (PV_B1_Carrier258.toQ c) (PV_B1_Orig258_PoleAdvance.advance i 0#usize)=true := by
  change PV_B1_258.all_slots_clear _ _ _=ok true ↔ _
  rw [PV_B1_PoleOutcome.truth_iff,PV_B1_HostPoleOutcome.length]
theorem falsity (ops : ExternalFuns) (v : Rows) (m : Array U16 64#usize) (c : HQ) :
    (selected ops).op258 v m c=ok false ↔ v.val.length≤1024 ∧
      ¬ (∀ i : Nat, i<v.val.length → PV_B1_Orig258_Op258Fold.keep (rows v) m
        (PV_B1_Carrier258.toQ c) (PV_B1_Orig258_PoleAdvance.advance i 0#usize)=true) := by
  change PV_B1_258.all_slots_clear _ _ _=ok false ↔ _
  rw [PV_B1_PoleFalseLaw.false_iff,PV_B1_HostPoleOutcome.length]
#print axioms truth
#print axioms falsity
end PV_B1_HostPoleTruth
