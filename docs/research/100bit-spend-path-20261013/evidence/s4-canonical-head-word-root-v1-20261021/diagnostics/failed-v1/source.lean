import S4HeadBatchTermsForwardRootV1
import MultiproofConeCanonical
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsCanonicalHeadWordRootV1
open AspisR1.MultiproofConeCanonical (bytesOf)
open AspisR1.OraclePortCompactDraft (little)

theorem array_bytes_list (a : Array Std.U8 4#usize) :
    List.ofFn (AspisR1.M31ParserArray.arrayBytes a)=bytesOf a.val := by
  apply List.ext_getElem
  · simp [bytesOf,a.property]
  · intro i hi hj
    simp [bytesOf,AspisR1.M31ParserArray.arrayBytes]

theorem literal_word_bound (a : Array Std.U8 4#usize)
    (h : little (bytesOf a.val)<2147483647) :
    (core.num.U32.from_le_bytes a).val<2147483647 := by
  apply (AspisR1.MultiproofConeEndian.strict_word_iff a).mpr
  rw [← AspisR1.MultiproofConeEndian.little_four,array_bytes_list]
  exact h

theorem current_m31_parser_forward (a : Array Std.U8 4#usize)
    (h : little (bytesOf a.val)<2147483647) :
    AspisR1DecodeKFullV10.aspis_core.field.M31.from_le_bytes a=
      .ok (some (core.num.U32.from_le_bytes a)) := by
  have hb := literal_word_bound a h
  have hn : ¬ core.num.U32.from_le_bytes a >= AspisR1DecodeKFullV10.aspis_core.field.P := by
    change ¬ 2147483647≤(core.num.U32.from_le_bytes a).val
    omega
  unfold AspisR1DecodeKFullV10.aspis_core.field.M31.from_le_bytes
  simp only [lift,bind_tc_ok]
  change (if core.num.U32.from_le_bytes a >= AspisR1DecodeKFullV10.aspis_core.field.P
    then .ok none else .ok (some (core.num.U32.from_le_bytes a)))=_
  rw [if_neg hn]
#print axioms array_bytes_list
#print axioms literal_word_bound
#print axioms current_m31_parser_forward
end AspisR1FastDotsCanonicalHeadWordRootV1
