import NKF_MasterBox
set_option autoImplicit false
noncomputable section
namespace NMX_MasterValue
open Aeneas Aeneas.Std Result
attribute [local instance] Classical.propDecidable
/-- Total raw decoder selection from the CLOSED symbolic pipeline. No buffer
contents or finite-field arithmetic is evaluated here. -/
def raw (b : Slice U8) : core.result.Result NJQ_Carrier.M NJQ_Carrier.F :=
 if size : b.val.length = 384 then NJQ_MasterCut.pipeline b size
 else .Err .WrongLength

def decoded (b : Slice U8) := NKF_BoxModel.tail (NJQ_Carrier.master_result (raw b))

theorem source (b : Slice U8) : NKF_MasterBox.reference b = ok (decoded b) := by
 unfold NKF_MasterBox.reference NKF_BoxModel.outer NJQ_Canonical.master decoded raw
 by_cases size : b.val.length = 384
 · rw [NJQ_MasterCut.model_closed b size]
   simp only [dif_pos size,NJQ_Canonical.mapOuter]
 · simp only [NJQ_Master.model,dif_neg size,NJQ_Canonical.mapOuter]
#print axioms source
end NMX_MasterValue
end
