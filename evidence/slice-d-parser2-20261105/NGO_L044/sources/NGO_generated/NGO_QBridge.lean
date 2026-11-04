import NGO_QCodec
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGO_QBridge
/-- Exact retained native stub association, not a same-name claim: E002 emits
the reference checked against both the frozen Q decoder (K005/K006) and the
EXACT NGD natural stub (K008/K009). All sixteen bytes and all four words. -/
theorem stub_law (arr : Array U8 16#usize) :
    (do let reply ← NGO_QRef.NGO_decode_le (Array.to_slice arr)
        ok (reply.map NGO_QAssociation.toActual)) =
      AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice arr) := by
  rw [NGO_QResult.emitted,NGO_QCodec.specification_codec,NGD_QDecodeLaw.stub_law]
  simp only [bind_tc_ok,Option.map_map,Function.comp_def]
  rfl
#print axioms stub_law
end NGO_QBridge
