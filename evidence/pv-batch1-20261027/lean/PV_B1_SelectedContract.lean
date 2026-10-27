import PV_B1_HostSumOption
import PV_B1_HostPoleTruth
import PV_B1_HostNoDivergence
import PV_B1_ReferenceOutcome
import PV_B1_CarrierResultRecovery
set_option autoImplicit false
noncomputable section
namespace PV_B1_SelectedContract
open Aeneas Aeneas.Std Result PV_B1_Transport
open PV_B1_Host PV_B1_Install
variable [ExternalTypes]
-- A typed source contract; native RunJoin/executable adequacy is still a P obligation.
theorem source_contract (ops : ExternalFuns) (xs : Slice HQ) (N : Usize) (x : HW)
    (v : Rows) (m : Array U16 64#usize) (c : HQ) :
    (selected ops).op230 xs=ok (PV_B1_HostSumSource.original_row xs) ∧
    (selected ops).op254 N x=resultMap (arrayMap PV_B1_CarrierWide.fromW)
      (PV_B1_PowersOriginal.weights.powers N (PV_B1_CarrierWide.toW x)) ∧
    (selected ops).op258 v m c=
      PV_B1_PoleOriginal.reference.all_slots_clear (rows v) m (PV_B1_Carrier258.toQ c) := by
  exact ⟨PV_B1_HostSumSource.op230_source ops xs,
    PV_B1_Install.op254_source ops N x,PV_B1_Install.op258_source ops v m c⟩
#print axioms source_contract
end PV_B1_SelectedContract
