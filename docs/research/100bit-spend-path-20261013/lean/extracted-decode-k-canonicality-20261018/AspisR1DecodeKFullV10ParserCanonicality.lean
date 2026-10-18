import AspisR1DecodeKFullV10.Funs

set_option autoImplicit false

namespace AspisR1DecodeKFullV10ParserCanonicality

open Aeneas Aeneas.Std Result

abbrev M31 := AspisR1DecodeKFullV10.aspis_core.field.M31
abbrev P := AspisR1DecodeKFullV10.aspis_core.field.P

theorem m31_from_le_bytes_success_canonical
    (bytes : Array U8 4#usize) (x : M31)
    (h : AspisR1DecodeKFullV10.aspis_core.field.M31.from_le_bytes bytes =
      Result.ok (some x)) :
    x.val < P.val := by
  unfold AspisR1DecodeKFullV10.aspis_core.field.M31.from_le_bytes at h
  simp only [lift, bind_tc_ok] at h
  change (if core.num.U32.from_le_bytes bytes >= P then ok none
    else ok (some (core.num.U32.from_le_bytes bytes))) = ok (some x) at h
  by_cases hge : core.num.U32.from_le_bytes bytes >= P
  · simp [hge] at h
  · simp only [hge, if_false, Result.ok.injEq, Option.some.injEq] at h
    subst x
    have hnot : ¬ P.val ≤ (core.num.U32.from_le_bytes bytes).val := by
      intro hle
      apply hge
      exact (UScalar.le_equiv P (core.num.U32.from_le_bytes bytes)).2 hle
    omega

#print axioms m31_from_le_bytes_success_canonical

end AspisR1DecodeKFullV10ParserCanonicality
