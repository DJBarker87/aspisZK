import FJi_Inputs
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJi_DecodeM31
open Aeneas Aeneas.Std Result
theorem value (bytes : Array U8 4#usize) (out : U32)
    (run : FIp_DotDecode.field.M31.from_le_bytes bytes=ok (some out)) :
    out=core.num.U32.from_le_bytes bytes ∧ out.val < 2147483647 := by
  unfold FIp_DotDecode.field.M31.from_le_bytes at run
  simp only [lift,bind_tc_ok] at run
  split at run
  · cases run
  · rename_i canonical
    cases Option.some.inj (Result.ok.inj run)
    refine ⟨rfl,?_⟩
    simp only [FIp_DotDecode.field.P] at canonical
    scalar_tac
#print axioms value
end AspisR1.FJi_DecodeM31
end
