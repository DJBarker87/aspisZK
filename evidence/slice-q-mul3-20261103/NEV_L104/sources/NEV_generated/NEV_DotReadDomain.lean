import NEV_DotRead
import Port3_PushFrame
set_option autoImplicit false
noncomputable section
namespace NEV_DotReadDomain
open Aeneas Aeneas.Std Result AspisR1
/-- Canonicality is a consequence of the actual scalar decoder's accepted
branch. Bytes remain completely unrestricted. -/
theorem scalar (bytes : Array U8 4#usize) (value : U32)
    (run : FIp_DotDecode.field.M31.from_le_bytes bytes=ok (some value)) :
    value.val<2147483647 := by
  simp only [FIp_DotDecode.field.M31.from_le_bytes,FIp_DotDecode.field.P,lift,bind_tc_ok] at run
  split at run
  · cases run
  · rename_i guard
    have same:=Option.some.inj (Result.ok.inj run)
    subst value
    change ¬ (2147483647≤(core.num.U32.from_le_bytes bytes).val) at guard
    omega
/-- A reached scalar is obtained from the SAME actual read, not an independent
canonical scalar oracle or successful whole-caller premise. -/
theorem reached (q : Array U8 608#usize) (slot term : Usize) (value : U32)
    (run : NEV_DotRead.read q slot term=ok value) : value.val<2147483647 := by
  unfold NEV_DotRead.read at run
  iterate 7 obtain ⟨x,_,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨bytes,_,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨decoded,decode,unwrap⟩:=Port3_PushFrame.bind_success _ _ _ run
  cases decoded with
  | none => cases unwrap
  | some actual =>
    have same : actual=value := Result.ok.inj unwrap
    subst value
    exact scalar bytes actual decode
#print axioms scalar
#print axioms reached
end NEV_DotReadDomain
end
