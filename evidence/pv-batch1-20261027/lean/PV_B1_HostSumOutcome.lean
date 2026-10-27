import PV_B1_HostSumSource
set_option autoImplicit false
noncomputable section
namespace PV_B1_HostSumOutcome
open Aeneas Aeneas.Std Result PV_B1_Transport
open PV_B1_Host PV_B1_Install PV_B1_HostSumSource
variable [ExternalTypes]
theorem wrong_length (ops : ExternalFuns) (xs : Slice HQ) (h : Slice.len xs≠1024#usize) :
    (selected ops).op230 xs=ok none := by
  rw [op230_source]
  simp only [original_row,h,if_false]
theorem exact_length (ops : ExternalFuns) (xs : Slice HQ) (h : Slice.len xs=1024#usize) :
    (selected ops).op230 xs=ok (some (xs.val.foldl PV_B1_HostSumValue.add PV_B1_HostSumValue.zero)) := by
  rw [op230_source]
  simp only [original_row,h,if_true]
theorem total (ops : ExternalFuns) (xs : Slice HQ) : ∃ y, (selected ops).op230 xs=ok y :=
  ⟨original_row xs,op230_source ops xs⟩
#print axioms wrong_length
#print axioms exact_length
#print axioms total
end PV_B1_HostSumOutcome
