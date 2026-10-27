import PV_B1_HostPoleOutcome
set_option autoImplicit false
noncomputable section
namespace PV_B1_HostFailureIndependence
open Aeneas Aeneas.Std Result PV_B1_Transport
open PV_B1_Host PV_B1_Install
variable [ExternalTypes]
-- Only the extracted array-bounds error. This is not the native OS event.
theorem same_length (ops : ExternalFuns) (a b : Rows) (ma mb : Array U16 64#usize)
    (ca cb : HQ) (h : a.val.length=b.val.length) :
    (selected ops).op258 a ma ca=fail .arrayOutOfBounds ↔
      (selected ops).op258 b mb cb=fail .arrayOutOfBounds := by
  rw [PV_B1_HostPoleOutcome.failure_iff,PV_B1_HostPoleOutcome.failure_iff,h]
#print axioms same_length
end PV_B1_HostFailureIndependence
