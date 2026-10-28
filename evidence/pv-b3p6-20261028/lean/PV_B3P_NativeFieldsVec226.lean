import PV_B3P_VecValue226
import PV_B3P_AppendFields226
import PV_B3P_EndianVerified226V3
namespace PV_B3P_NativeFieldsVec226
open Aeneas Aeneas.Std PV_B3P_226V3 PV_B3P_RustResult PV_B3P_ByteLayout226V3
set_option autoImplicit false
abbrev E := aspis_core.state_only_prefix.r0.Error

def wordSlice (v : U32) : Slice U8 :=
  ⟨(core.num.U32.to_le_bytes v).val, by
    rw [← PV_B3P_EndianVerified226V3.word_bytes]
    change 4 ≤ Usize.max
    scalar_tac⟩
theorem word_slice_value (v : U32) : (wordSlice v).val = wordBytes v :=
  (PV_B3P_EndianVerified226V3.word_bytes v).symm

def fieldsVec (out : alloc.vec.Vec U8) : List U32 →
    Result (core.result.Result (alloc.vec.Vec U8) E)
  | [] => .ok (.Ok out)
  | v::xs => if v < 2147483647#u32 then do
      let out' ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out (wordSlice v)
      fieldsVec out' xs
    else .ok (.Err aspis_core.state_only_prefix.r0.Error.Public)

set_option backward.isDefEq.respectTransparency false in
theorem complete_result (out : alloc.vec.Vec U8) (xs : List U32)
    (hb : out.val.length + 4*xs.length ≤ Usize.max) :
    mapR (fun v : alloc.vec.Vec U8 => v.val) (fieldsVec out xs) =
      PV_B3P_AppendFields226.nativeFields out.val xs := by
  induction xs generalizing out with
  | nil => rfl
  | cons v xs ih =>
    have hlen : (wordSlice v).val.length = 4 := by
      rw [word_slice_value]
      rfl
    by_cases hc : v < 2147483647#u32
    · obtain ⟨out',hout',hval⟩ := PV_B3P_VecValue226.u8_extend out (wordSlice v)
        (by rw [hlen]; simp only [List.length_cons] at hb; omega)
      have hb' : out'.val.length + 4*xs.length ≤ Usize.max := by
        rw [hval,List.length_append,hlen]
        simp only [List.length_cons] at hb
        omega
      simp only [fieldsVec,hc,↓reduceIte,hout',bind_tc_ok]
      rw [ih out' hb',PV_B3P_AppendFields226.nativeFields]
      simp only [hc,↓reduceIte,hval,word_slice_value]

    · simp only [fieldsVec,hc,↓reduceIte,mapR,bindR,PV_B3P_AppendFields226.nativeFields]

#print axioms word_slice_value
#print axioms complete_result
end PV_B3P_NativeFieldsVec226
