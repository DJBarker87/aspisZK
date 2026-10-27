import PV_B1_ReferenceInstall
import PV_B1_HostPowersTotal
import PV_B1_HostSumOutcome
import PV_B1_HostPoleOutcome
set_option autoImplicit false
noncomputable section
namespace PV_B1_ReferenceOutcome
open Aeneas Aeneas.Std Result PV_B1_Transport
open PV_B1_Host PV_B1_Install
variable [ExternalTypes]
theorem sum_total (ops : ExternalFuns) (xs : Slice HQ) :
    ∃ y, (PV_B1_ReferenceInstall.selected ops).op230 xs=ok y := by
  rw [←PV_B1_ReferenceInstall.source_eq]
  exact PV_B1_HostSumOutcome.total ops xs
theorem powers_total (ops : ExternalFuns) (N : Usize) (x : HW) :
    ∃ y, (PV_B1_ReferenceInstall.selected ops).op254 N x=ok y := by
  rw [←PV_B1_ReferenceInstall.source_eq]
  exact PV_B1_HostPowersTotal.total ops N x
theorem pole_failure (ops : ExternalFuns) (v : Rows) (m : Array U16 64#usize) (c : HQ) :
    (PV_B1_ReferenceInstall.selected ops).op258 v m c=fail .arrayOutOfBounds ↔
      1024<v.val.length := by
  rw [←PV_B1_ReferenceInstall.source_eq]
  exact PV_B1_HostPoleOutcome.failure_iff ops v m c
#print axioms sum_total
#print axioms powers_total
#print axioms pole_failure
end PV_B1_ReferenceOutcome
