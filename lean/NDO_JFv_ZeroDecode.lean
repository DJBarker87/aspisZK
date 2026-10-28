import RPz7_PAln_InactiveDecode
import NDO_JFw_Frames
import NDO_JFz_Scan01
set_option autoImplicit false
namespace AspisR1.JFv_ZeroDecode
open Aeneas Aeneas.Std Result
open RetainedFieldByteCodec StrictWideByteCodec WideParserArrayHalves

theorem parser (input : Slice U8) (zero : input.val = List.replicate 32 0#u8) :
    ∃ value, AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes_unrolled input = ok (some value) := by
  have len : input.val.length = 32 := by rw [zero,List.length_replicate]
  let arr : Array U8 32#usize := ⟨input.val,len⟩
  have same : Array.to_slice arr = input := by cases input;rfl
  have bytes : arrayBytes32 arr = fun _ => 0 := by
    funext i
    unfold arrayBytes32
    change AspisV8R19.SqueezeOracleBridge.decodeByte (input.val[i.val]'_) = 0
    simp only [zero,List.getElem_replicate]
    rfl
  rw [←same,UnrolledWideParserRefinement.source_refines,bytes]
  simp only [decodeWideLE,lowBytes,highBytes,decodeQM31LE,qm31LimbBytes,decodeWordLE]
  simp

#print axioms parser
end AspisR1.JFv_ZeroDecode
