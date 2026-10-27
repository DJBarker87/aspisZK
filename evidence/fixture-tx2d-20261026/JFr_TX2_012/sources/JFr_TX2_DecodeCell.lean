import FIp_DotDecode
set_option autoImplicit false
namespace AspisR1.JFr_TX2_DecodeCell
open Aeneas Aeneas.Std Result

def cell (raw : Array U8 104#usize) (t : Fin 26) : Array U8 4#usize :=
  ⟨(raw.val.drop (4*t.val)).take 4, by
    simp only [List.length_take,List.length_drop,raw.property]
    have := t.isLt
    change min 4 (104-4*t.val)=4
    omega⟩

theorem source (a : Array U8 4#usize) (v : U32)
    (decoded : core.num.U32.from_le_bytes a=v)
    (canonical : v.val<2147483647) :
    FIp_DotDecode.field.M31.from_le_bytes a=ok (some v) := by
  simp only [FIp_DotDecode.field.M31.from_le_bytes,decoded,lift,bind_tc_ok]
  rw [if_neg]
  change ¬ v.val≥2147483647
  omega

#print axioms source
end AspisR1.JFr_TX2_DecodeCell
