import PV_B1_Install
import PV_B1_PowersTotal
set_option autoImplicit false
noncomputable section
namespace PV_B1_HostPowersTotal
open Aeneas Aeneas.Std Result PV_B1_Transport
open PV_B1_Host PV_B1_Install
variable [ExternalTypes]
theorem total (ops : ExternalFuns) (N : Usize) (x : HW) :
    ∃ y, (selected ops).op254 N x=ok y := by
  obtain ⟨y,hy⟩ := PV_B1_PowersTotal.total N (PV_B1_CarrierWide.toW x)
  refine ⟨arrayMap PV_B1_CarrierWide.fromW y,?_⟩
  change resultMap _ _= _
  rw [hy]
  rfl
#print axioms total
end PV_B1_HostPowersTotal
