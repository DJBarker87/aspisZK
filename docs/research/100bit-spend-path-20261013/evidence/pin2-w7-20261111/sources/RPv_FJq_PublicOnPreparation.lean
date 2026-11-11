import RPv_FJq_PublicWire
import ExtractedPublicPreparationBinding
import PIN2W7_TranscriptCopy
set_option autoImplicit false
/-! PIN2 W11 (2026-11-11): restated on the PIN2 public transcript (W7 pattern).
* Premise `prepared`: the PIN2 `public_transcript` of `PreparationBinding.toPIN2
  (preparationPublic s)`, with `D` and `out` carried by `PIN2W7_TranscriptCopy`; the binder
  types of `D` and `out` are unchanged (frozen).
* Conclusion, serializer conjunct: frozen `AspisR1PublicSerializer` `public_bytes
  (toSerializer s)` -> PIN2 `public_bytes (toSerializer s)` (W3c: `toSerializer s` is now the
  PIN2 carrier, `RawBridge431.Public`; these are the bytes the PIN2 verifier serializes).
* `parsePublic` and the frozen `SemanticTranscript.new D hash bytes c1 = ok (.Ok out)`
  conjuncts are textually unchanged (the latter by `PIN2W7_TranscriptCopy.new_eq`).
* Public-model conjunct: `ofPublic` of `PIN2W11_PublicCopy.nativePIN2` (W3c retyped `ofPublic`
  to the PIN2 struct; see `RPv_FJq_PublicWire`). -/
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
    (prepared : AspisR1PublicPreparationPIN2.r1_semantic.public_transcript (PIN2W7_TranscriptCopy.digest D)
      (PreparationBinding.toPIN2 (PreparationBinding.preparationPublic s)) hash c1=
      ok (.Ok (PIN2W7_TranscriptCopy.transcript out))) :
    ∃ (bytes : alloc.vec.Vec U8) (wire : SemanticPublicWire.Wire),
      AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
        (AspisR1TerminalDecoder.PublicBinding.toSerializer s)=ok (.Ok bytes) ∧
      SemanticPublicWire.parsePublic (bytes.val.map AspisR1PublicSerializer.RawBridge431.rawByte)=
        some (SemanticPublicWire.toPublic wire) ∧
      r1_wire.SemanticTranscript.new D hash (alloc.vec.Vec.deref bytes) c1=ok (.Ok out) ∧
      SpendDataMap.mapPublic embed (FIw_PublicModel.ofPublic (PIN2W11_PublicCopy.nativePIN2
        (PreparationBinding.preparationPublic s)))=
        SpendDataMap.mapPublic ExactBaseProjection.embed (SemanticPublicWire.toPublic wire) := by
  obtain ⟨bytes,wire,serialized,mapped,parsed,new⟩:=
    PreparationBinding.decoder_helper_parsePublic (PIN2W7_TranscriptCopy.digest D) asf8 s hash c1
      (PIN2W7_TranscriptCopy.transcript out) decoded prepared
  exact ⟨bytes,wire,serialized,parsed,PIN2W7_TranscriptCopy.new_eq D hash _ c1 out new,
    FJq_PublicWire.value s wire mapped⟩
#print axioms value
end AspisR1.FJq_PublicOnPreparation
end
