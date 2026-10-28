import NDO_JFv_RoundArithmetic
set_option autoImplicit false
namespace AspisR1.JFv_InitialValue
open Aeneas Aeneas.Std Result WP
open AspisR1PublicPreparation AspisS1ExtractedRoundChildren

theorem source (bytes : Slice U8) (pre : r1_wire.Prefix)
    (parsed : PrefixAdapter.parseAccepted bytes=ok (.Ok pre)) :
    ∃ vr values running,
      r1_wire.Prefix.validated_record pre 14#u8=ok (.Ok vr) ∧
      decodeMain 1#usize vr 0#usize=ok (.Ok values) ∧
      Array.index_usize values 0#usize=ok running ∧ JFv_RoundArithmetic.Canonical running := by
  obtain ⟨vr,values,record,decode⟩ := JFv_SemanticDecode.initial bytes pre parsed
  have canon := JFv_DecodeCanonical.source vr 0#usize values decode
  have read : Array.index_usize values 0#usize
      ⦃ running => running=values.val[0]'(by simp only [values.property];decide) ⦄ := by step*
  obtain ⟨running,call,same⟩ := WP.spec_imp_exists read
  refine ⟨vr,values,running,record,decode,call,?_⟩
  rw [same]
  exact canon ⟨0,by decide⟩

#print axioms source
end AspisR1.JFv_InitialValue
