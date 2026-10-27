import XSe_ValidatorIndex
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSe_ValidatorTransport
/-- Complete native-domain validator equation, including the exact first
failing row/index, empty payloads and ignored tails. No accepted-record premise. -/
theorem source (row : U8) (payload : Slice U8) (domain : payload.val.length≤3712) :
 XRo_Join_Carriers.mapR (XRo_Join_Carriers.inner id XRu_ParserShapes.error)
  (r1_wire.validate_record_fields row payload)=
 AspisR1PrefixAggregateParser.r1_wire.validate_record_fields row payload := by
 rw [XSe_ValidatorScan.source row payload domain,XSe_ValidatorIndex.source]
 unfold r1_wire.validate_record_fields XSe_BooleanScan.result XSe_ValidatorIndex.bad
 cases h : (List.range (payload.val.length/32)).find?
   (fun i => !XRn_Join_Bytes.validChunk 8 true ((payload.val.drop (32*i)).take 32)) with
 | none => rfl
 | some i =>
   dsimp only
   split <;> rfl
#print axioms source
end XSe_ValidatorTransport
