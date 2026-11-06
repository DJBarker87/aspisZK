import NKU_HeaderStep
import NKU_HeaderEnd
import NKU_InputAt
import NKU_Roots
set_option autoImplicit false
noncomputable section
namespace NKU_HeaderState
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NKU_InputAt
theorem returned {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (s out : NKU.State) (actual : (NKU_HeaderStep.run d s).result=ok (.Ok ((),out))) :
 out.frame=s.frame ∧ out.reader=s.reader ∧ out.owned=s.owned ∧
 out.frame.checkpoint.val.length=1768 ∧ out.decoded.endAt=some 1736#usize := by
 cases head : (NKU_HeaderValue.value d s.frame.checkpoint .S2).result with
 | fail err =>
  simp only [NKU_HeaderStep.run,NJU_Log.erase_bind,head,bind_tc_fail] at actual
  cases actual
 | div =>
  simp only [NKU_HeaderStep.run,NJU_Log.erase_bind,head,bind_tc_div] at actual
  cases actual
 | ok reply =>
  cases reply with
  | Err err =>
   simp only [NKU_HeaderStep.run,NJU_Log.erase_bind,head,bind_tc_ok,NKK_Try.branch,NJU_Log.erase_pure] at actual
   cases actual
  | Ok pair =>
   have size:=NKU_HeaderDomain.length d s.frame.checkpoint pair head
   have ending:=NKU_HeaderEnd.returned d s.frame.checkpoint pair head
   simp only [NKU_HeaderStep.run,NJU_Log.erase_bind,head,bind_tc_ok,NKK_Try.branch,NJU_Log.erase_pure] at actual
   cases actual
   exact ⟨rfl,rfl,rfl,size,congrArg some ending⟩
theorem root_entry (s : NKU.State) (size : s.frame.checkpoint.val.length=1768) :
 At {s with reader := NKU_Roots.entry s} 80 := ⟨size,rfl,rfl⟩
#print axioms returned
#print axioms root_entry
end NKU_HeaderState
