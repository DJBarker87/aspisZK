import PV_B3P_FrontierModel13227
namespace PV_B3P_Binding13227
open Aeneas Aeneas.Std PV_B3P_227 Result
set_option autoImplicit false
/-- The pure byte-content projection after successful allocation; this is not
an unconditional claim that the native allocator succeeds. -/
def append_word_contents13 (out : List U8) (value : U32) : Result (List U8) :=
  .ok (out ++ (core.num.U32.to_le_bytes value).val)

theorem fields_good_prefix13 (out : List U8) (value : U32) (values : List U32)
    (good : ¬value ≥ 2147483647#u32) :
    fields_model13 append_word_contents13 out (value::values) =
      fields_model13 append_word_contents13 (out ++ (core.num.U32.to_le_bytes value).val) values := by
  simp only [fields_model13,good,if_false,append_word_contents13,bind_tc_ok]

theorem fields_rejected_suffix_keeps_prefix13 (out : List U8) (first bad : U32)
    (tail : List U32) (good : ¬first ≥ 2147483647#u32) (invalid : bad ≥ 2147483647#u32) :
    fields_model13 append_word_contents13 out (first::bad::tail) =
      .ok (.Err .Public,out ++ (core.num.U32.to_le_bytes first).val) := by
  rw [fields_good_prefix13 out first (bad::tail) good]
  exact fields_reject13 _ _ bad tail invalid
#print axioms fields_good_prefix13
#print axioms fields_rejected_suffix_keeps_prefix13
end PV_B3P_Binding13227
