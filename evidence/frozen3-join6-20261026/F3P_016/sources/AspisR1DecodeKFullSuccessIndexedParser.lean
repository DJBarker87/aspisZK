import AspisR1DecodeKFullSuccessReadback
import AspisR1DecodeKFullValueTrace

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1DecodeKFullSuccessIndexedParser

abbrev QM := AspisR1DecodeKFullV10.aspis_core.field.QM31
abbrev US := Std.UScalar Std.UScalarTy.Usize

open AspisR1DecodeKFullSuccessReadback
open AspisR1DecodeKFullValueTrace

theorem decode_k_success_indexed_parser
    (n : US) (self : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord)
    (offsetValues : US) (out : Array QM n)
    (h : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k n self offsetValues =
      .ok (.Ok out)) :
    ∃ byteOffset : US,
      lift (Usize.checked_mul offsetValues 32#usize) = .ok (some byteOffset) ∧
      ∀ j : Fin n, j.val < n.val →
        ∃ q : QM,
          AspisR1DecodeKFullV10.r1_wire.ValidatedRecord.decode_k_value
            { row := self.row, framed := self.framed } byteOffset
            (UScalar.ofNatCore j.val (by have := j.isLt; scalar_tac)) offsetValues =
              .ok (.Ok q) ∧
          out.val[j.val]'(by simpa [out.property] using j.isLt) = q ∧
          Nonempty (ParserTrace { row := self.row, framed := self.framed }
            byteOffset
            (UScalar.ofNatCore j.val (by have := j.isLt; scalar_tac))
            offsetValues q) := by
  obtain ⟨byteOffset, hOffset, hvalues⟩ := decode_k_success_readback n self offsetValues out h
  refine ⟨byteOffset, hOffset, ?_⟩
  intro j hj
  obtain ⟨q, hcall, hcell⟩ := hvalues j hj
  have htrace := decode_k_value_success_parser_trace
    { row := self.row, framed := self.framed } byteOffset
    (UScalar.ofNatCore j.val (by have := j.isLt; scalar_tac)) offsetValues q hcall
  exact ⟨q, hcall, hcell, htrace⟩

#print axioms decode_k_success_indexed_parser
end AspisR1DecodeKFullSuccessIndexedParser
