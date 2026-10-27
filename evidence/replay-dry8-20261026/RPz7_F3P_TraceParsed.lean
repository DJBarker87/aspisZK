import F3P_TraceWindow
import RPz7_F3P_StrictLowParser
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3P_TraceParsed
open Aeneas Aeneas.Std Result AspisR1DecodeKFullValueTrace

theorem parsed (r : AspisR1DecodeKFullV10.r1_wire.ValidatedRecord)
    (byteOffset j offset : Usize) (q : QM) (t : ParserTrace r byteOffset j offset q) :
    ∃ value : SemanticCoefficientCodec.LowWide,
      SemanticCoefficientCodec.decodeLow
        (MultiproofConeCanonical.bytesOf ((ParserTrace.payloadData t).val.drop
          (byteOffset.val+32*j.val) |>.take 16)++List.replicate 16 0)=some value ∧
      value.val=LiteralOpeningView.eK (F3L_RhoMeaning.decode (AspisS1ExtractedRoundChildren.decoderQMToMain q)) := by
  have length : (ParserTrace.inputBytes t).val.length=16 := by
    rw [F3P_TraceInput.bytes]
    rfl
  let arr : Array Std.U8 16#usize := ⟨(ParserTrace.inputBytes t).val,length⟩
  have same : Array.to_slice arr=ParserTrace.inputBytes t := by
    apply Subtype.ext
    rfl
  have source := F3P_StrictLowParser.parsed arr q (by rw [same];exact ParserTrace.hparse t)
  change ∃ value : SemanticCoefficientCodec.LowWide,
      SemanticCoefficientCodec.decodeLow
        (MultiproofConeCanonical.bytesOf (ParserTrace.inputBytes t).val++List.replicate 16 0)=some value ∧
      value.val=LiteralOpeningView.eK (F3L_RhoMeaning.decode (AspisS1ExtractedRoundChildren.decoderQMToMain q)) at source
  rw [F3P_TraceWindow.window,F3P_TraceStart.start] at source
  exact source

#print axioms parsed
end AspisR1.F3P_TraceParsed
end
