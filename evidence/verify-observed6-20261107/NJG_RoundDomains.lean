import NJG_RoundCode
import NDO_JFv_RoundArithmetic
set_option autoImplicit false
namespace AspisR1.NJG_RoundDomains
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisS1ExtractedRoundChildren

/-- SAME parsed predecessor supplies the actual polynomial and the complete
canonical boundary packet. No decoder/boundary output is a root premise. -/
theorem polynomial (bytes : Slice U8) (pre : AspisR1PrefixAggregateParser.r1_wire.Prefix)
 (parsed : AspisR1PrefixAggregateParser.r1_wire.Prefix.parse bytes=ok (.Ok pre))
 (round : Usize) (bound : round.val<10) :
 ∃ record coefficients boundary,
 r1_wire.Prefix.validated_record (PrefixAdapter.fromOld pre) (NJG_RoundProducer.row round bound)=ok (.Ok record) ∧
 decodeMain 28#usize record 0#usize=ok (.Ok coefficients) ∧
 (∀ i : Fin 28,JFv_RoundArithmetic.Canonical (coefficients.val[i.val]'(by simpa only [coefficients.property,show (28#usize).val=28 from rfl] using i.isLt))) ∧
 generatedMainBoundary coefficients=ok boundary ∧ JFv_RoundArithmetic.Canonical boundary := by
 have main : PrefixAdapter.parseAccepted bytes=ok (.Ok (PrefixAdapter.fromOld pre)) := by
  simp only [PrefixAdapter.parseAccepted,parsed,bind_tc_ok]
 obtain ⟨record,coefficients,getter,decoder⟩:=JFv_SemanticDecode.round bytes (PrefixAdapter.fromOld pre) main ⟨round.val,bound⟩
 have canonical : ∀ i : Fin 28,JFv_RoundArithmetic.Canonical
  (coefficients.val[i.val]'(by simpa only [coefficients.property,show (28#usize).val=28 from rfl] using i.isLt)) :=
   JFv_DecodeCanonical.source record 0#usize coefficients decoder
 obtain ⟨boundary,call,bc⟩:=JFv_RoundArithmetic.boundary coefficients canonical
 exact ⟨record,coefficients,boundary,getter,decoder,canonical,call,bc⟩

#print axioms polynomial
end AspisR1.NJG_RoundDomains
