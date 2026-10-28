import NDO_JFr_DecodeCell
set_option autoImplicit false
namespace AspisR1.JFr_EncodedCell
open Aeneas Aeneas.Std Result
open RetainedFieldByteCodec

theorem parser (arr : Array U8 16#usize) (limbs : QM31Limbs)
    (encoded : CandidateParserByteOrder.arrayBytes16 arr=encodeQM31LE limbs) :
    AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice arr)=
      ok (some (ActualDecodeKStrictQM31Parser.limbsToActual limbs)) := by
  rw [ActualDecodeKStrictQM31Parser.source_refines,encoded,decodeQM31LE_encodeQM31LE]
  rfl

#print axioms parser
end AspisR1.JFr_EncodedCell
