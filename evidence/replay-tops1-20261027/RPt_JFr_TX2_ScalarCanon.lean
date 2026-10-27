import RPt_JFr_TX2_DecodeCell
set_option autoImplicit false
namespace AspisR1.JFr_TX2_ScalarCanon
open Aeneas Aeneas.Std Result

theorem source (bytes : Array U8 4#usize) (v : U32)
    (run : FIp_DotDecode.field.M31.from_le_bytes bytes=ok (some v)) :
    v.val<2147483647 := by
  unfold FIp_DotDecode.field.M31.from_le_bytes at run
  simp only [lift,bind_tc_ok] at run
  split at run
  · cases run
  · rename_i below
    have same := Option.some.inj (Result.ok.inj run)
    subst v
    rw [FIp_DotDecode.field.P] at below
    change ¬ (core.num.U32.from_le_bytes bytes).val≥2147483647 at below
    omega

#print axioms source
end AspisR1.JFr_TX2_ScalarCanon
