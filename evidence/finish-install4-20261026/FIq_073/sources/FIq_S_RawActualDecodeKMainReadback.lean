import FIq_S_RawActualDecodeKMainAdapter
import AspisR1DecodeKFullSuccessIndexedParser

set_option autoImplicit false
namespace AspisR1PublicPreparation.RawActualDecodeKMainReadback
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.RawSemanticFieldOwnerAdapter
open AspisR1PublicPreparation.RawActualDecodeKMainAdapter

/-- Every coefficient returned by the concrete Main decoder comes from the
same actual indexed parser calls on the input record's row and framed bytes.
This transports the retained byte-readback proof, rather than supplying a
coefficient/byte correspondence premise. -/
theorem decodeMain_success_indexed_parser
    (n : Usize) (r : MainRecord) (offset : Usize) (out : Array MainQM n)
    (h : decodeMain n r offset = .ok (.Ok out)) :
    ∃ byteOffset : Usize,
      lift (Usize.checked_mul offset 32#usize) = .ok (some byteOffset) ∧
      ∀ j : Fin n,
        ∃ q : DecodeQM,
          AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_value
            (recordToDecoder r) byteOffset
            (UScalar.ofNatCore j.val (by have := j.isLt; scalar_tac)) offset = .ok (.Ok q) ∧
          out.val[j.val]'(by simpa [out.property] using j.isLt) = decoderQMToMain q ∧
          Nonempty (AspisR1DecodeKFullValueTrace.ParserTrace (recordToDecoder r)
            byteOffset (UScalar.ofNatCore j.val (by have := j.isLt; scalar_tac)) offset q) ∧
          Canonical (mainToProbe (decoderQMToMain q)) := by
  obtain ⟨actual, hactual, hout⟩ := decodeMain_success_inv n r offset out h
  obtain ⟨byteOffset, hOffset, hvalues⟩ :=
    AspisR1DecodeKFullSuccessIndexedParser.decode_k_success_indexed_parser
      n (recordToDecoder r) offset actual hactual
  have hcanonical := AspisR1DecodeKFullSuccessCanonicality.decode_k_success_canonical
    n (recordToDecoder r) offset actual hactual
  refine ⟨byteOffset, hOffset, ?_⟩
  intro j
  obtain ⟨q, hcall, hcell, htrace⟩ := hvalues j j.isLt
  refine ⟨q, hcall, ?_, htrace, ?_⟩
  · rw [← hout]
    simpa only [decoderArrayToMain, List.getElem_map] using congrArg decoderQMToMain hcell
  · exact decoder_canonical_to_main q (hcell ▸ hcanonical j)

#print axioms decodeMain_success_indexed_parser
end AspisR1PublicPreparation.RawActualDecodeKMainReadback
