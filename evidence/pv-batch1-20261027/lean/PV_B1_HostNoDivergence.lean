import PV_B1_HostPowersTotal
import PV_B1_HostSumOutcome
import PV_B1_HostPoleOutcome
set_option autoImplicit false
noncomputable section
namespace PV_B1_HostNoDivergence
open Aeneas Aeneas.Std Result PV_B1_Transport
open PV_B1_Host PV_B1_Install
variable [ExternalTypes]
theorem sum (ops : ExternalFuns) (xs : Slice HQ) : (selected ops).op230 xs≠div := by
  obtain ⟨y,hy⟩ := PV_B1_HostSumOutcome.total ops xs
  rw [hy]; intro h; cases h
theorem powers (ops : ExternalFuns) (N : Usize) (x : HW) : (selected ops).op254 N x≠div := by
  obtain ⟨y,hy⟩ := PV_B1_HostPowersTotal.total ops N x
  rw [hy]; intro h; cases h
theorem pole (ops : ExternalFuns) (v : Rows) (m : Array U16 64#usize) (c : HQ) :
    (selected ops).op258 v m c≠div :=
  PV_B1_PoleOutcome.never_diverges (rows v) m (PV_B1_Carrier258.toQ c)
#print axioms sum
#print axioms powers
#print axioms pole
end PV_B1_HostNoDivergence
