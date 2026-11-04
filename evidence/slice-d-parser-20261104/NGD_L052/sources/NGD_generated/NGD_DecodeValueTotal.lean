import NGD_DecodeGeometry
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace NGD_DecodeValueTotal
open AspisR1DecodeKFullV10

@[progress] theorem q_parser_spec (arr : Array U8 16#usize) :
    aspis_core.field.QM31.from_le_bytes (Array.to_slice arr) ⦃ out =>
      out = (AspisR1.RetainedFieldByteCodec.decodeQM31LE
        (AspisR1.CandidateParserByteOrder.arrayBytes16 arr)).map
          AspisR1.ActualDecodeKStrictQM31Parser.limbsToActual ⦄ := by
  rw [NGD_QDecodeLaw.stub_law]
  simp

@[progress] theorem payload_spec (r : r1_wire.ValidatedRecord) (bound : 5 ≤ r.framed.val.length) :
    r1_wire.ValidatedRecord.payload r ⦃ out => out.val = r.framed.val.drop 5 ⦄ := by
  unfold r1_wire.ValidatedRecord.payload
  step*

/-- Totality of the actual emitted sixteen-read helper on every fitting
original payload window, including noncanonical inputs and error replies. -/
theorem value_total (r : r1_wire.ValidatedRecord) (off byteOffset n i : Usize)
    (minlen : 5 ≤ r.framed.val.length) (cap : r.framed.val.length ≤ 3717)
    (start : byteOffset.val = 32*off.val) (positive : 0<n.val) (live : i.val<n.val)
    (range : 32*off.val+32*n.val ≤ r.framed.val.length-5) :
    ∃ reply, r1_wire.ValidatedRecord.decode_k_value r byteOffset i off = ok reply := by
  have geometry := NGD_DecodeGeometry.fitting r.framed.val.length off.val n.val i.val minlen cap positive live range
  have spec : r1_wire.ValidatedRecord.decode_k_value r byteOffset i off ⦃ _ => True ⦄ := by
    unfold r1_wire.ValidatedRecord.decode_k_value
    step*
    simp only [s_post]
    step*
    simp [core.option.Option.ok_or]
  obtain ⟨reply,call,_⟩ := WP.spec_imp_exists spec
  exact ⟨reply,call⟩
#print axioms q_parser_spec
#print axioms payload_spec
#print axioms value_total
end NGD_DecodeValueTotal
