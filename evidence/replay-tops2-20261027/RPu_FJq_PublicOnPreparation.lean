import RPu_FJq_PublicWire
import ExtractedPublicPreparationBinding
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJq_PublicOnPreparation
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open FIz_ConcretePack (embed)
/-- Actual ASF8 decode and public transcript success identify the literal
parsed semantic public AND its full native model, on the SAME statement. -/
theorem value {H : Type} (D : aspis_core.Digest32 H) (asf8 : Slice U8)
    (s : AspisR1TerminalDecoder.PublicBinding.Statement) (hash : H)
    (c1 : Array U8 32#usize) (out : r1_wire.SemanticTranscript H)
    (decoded : AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1
      asf8=ok (.Ok s))
    (prepared : r1_semantic.public_transcript D (PreparationBinding.preparationPublic s) hash c1=ok (.Ok out)) :
    ∃ (bytes : alloc.vec.Vec U8) (wire : SemanticPublicWire.Wire),
      AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
        (AspisR1TerminalDecoder.PublicBinding.toSerializer s)=ok (.Ok bytes) ∧
      SemanticPublicWire.parsePublic (bytes.val.map AspisR1PublicSerializer.RawBridge431.rawByte)=
        some (SemanticPublicWire.toPublic wire) ∧
      r1_wire.SemanticTranscript.new D hash (alloc.vec.Vec.deref bytes) c1=ok (.Ok out) ∧
      SpendDataMap.mapPublic embed (FIw_PublicModel.ofPublic (FJa_PublicCopy.native
        (PreparationBinding.preparationPublic s)))=
        SpendDataMap.mapPublic ExactBaseProjection.embed (SemanticPublicWire.toPublic wire) := by
  obtain ⟨bytes,wire,serialized,mapped,parsed,new⟩:=
    PreparationBinding.decoder_helper_parsePublic D asf8 s hash c1 out decoded prepared
  exact ⟨bytes,wire,serialized,parsed,new,FJq_PublicWire.value s wire mapped⟩
#print axioms value
end AspisR1.FJq_PublicOnPreparation
end
