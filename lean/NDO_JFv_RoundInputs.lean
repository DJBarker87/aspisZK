import NDO_JFv_RoundArithmetic
set_option autoImplicit false
namespace AspisR1.JFv_RoundInputs
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisS1ExtractedRoundChildren

theorem success (bytes : Slice U8) (pre : r1_wire.Prefix)
    (parsed : PrefixAdapter.parseAccepted bytes=ok (.Ok pre)) (r : Fin 10) :
    ∃ vr coefficients boundary,
      r1_wire.Prefix.validated_record pre (JFv_SemanticDecode.roundRow r)=ok (.Ok vr) ∧
      decodeMain 28#usize vr 0#usize=ok (.Ok coefficients) ∧
      (∀ i : Fin 28,JFv_RoundArithmetic.Canonical
        (coefficients.val[i.val]'(by simpa only [coefficients.property,show (28#usize).val=28 from rfl] using i.isLt))) ∧
      generatedMainBoundary coefficients=ok boundary ∧ JFv_RoundArithmetic.Canonical boundary := by
  obtain ⟨vr,coefficients,record,decode⟩ := JFv_SemanticDecode.round bytes pre parsed r
  have canon : ∀ i : Fin 28,JFv_RoundArithmetic.Canonical
      (coefficients.val[i.val]'(by simpa only [coefficients.property,show (28#usize).val=28 from rfl] using i.isLt)) :=
    JFv_DecodeCanonical.source vr 0#usize coefficients decode
  obtain ⟨boundary,call,canonical⟩ := JFv_RoundArithmetic.boundary coefficients canon
  exact ⟨vr,coefficients,boundary,record,decode,canon,call,canonical⟩

#print axioms success
end AspisR1.JFv_RoundInputs
