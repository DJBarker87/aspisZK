import RPv_FJq_SourceLiteralPublic
import RPv_FJa_PublicOnPreparation
set_option autoImplicit false
/-! PIN2 W11 (2026-11-11): restated on the PIN2 public transcript (W7 pattern).
* Premise `init`: the PIN2 `public_transcript` of `PreparationBinding.toPIN2 pub`, with `D`
  and `t0` carried by `PIN2W7_TranscriptCopy` (binder types unchanged, frozen).
* Premise `serialized`: frozen `public_bytes pub` -> PIN2 `public_bytes (toPIN2 pub)` (the
  form `FJt_PublicLog.value` now supplies, W11).
* Conclusion: the `Bounds (FJa_PublicCopy.native pub)` conjunct is textually unchanged; the
  public-model conjunct applies `ofPublic` to `PIN2W11_PublicCopy.nativePIN2 pub` (W3c retyped
  `ofPublic` to the PIN2 struct; see `RPv_FJq_PublicWire`).
* Proof: the release proof with the PIN2 lemmas; the `SerializerWhole.serializer_eq` step is
  dropped because W3c's `projection_eq` now lands on the PIN2 `public_bytes`. -/
noncomputable section
namespace AspisR1.FJt_PublicJoin
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open FIz_ConcretePack (embed)

theorem value {H : Type} (D : aspis_core.Digest32 H)
    (pub : FIq_Carriers.Public) (s : AspisR1TerminalDecoder.PublicBinding.Statement)
    (physical : Slice U8)
    (decoded : AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1
      physical=ok (.Ok s))
    (same : pub=PreparationBinding.preparationPublic s)
    (hash : H) (root : Array U8 32#usize) (t0 : r1_wire.SemanticTranscript H)
    (init : AspisR1PublicPreparationPIN2.r1_semantic.public_transcript (PIN2W7_TranscriptCopy.digest D)
      (PreparationBinding.toPIN2 pub) hash root=ok (.Ok (PIN2W7_TranscriptCopy.transcript t0)))
    (encoded : alloc.vec.Vec U8)
    (serialized : AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
      (PreparationBinding.toPIN2 pub)=ok (.Ok encoded))
    (literal : LiteralTranscript.Public) (literalPub : R0P.Public SemanticPublicWire.M31)
    (bytesSame : literal.pubBytes=SourceDigestAddresses.rawBytes encoded.deref)
    (parsed : SemanticPublicWire.parsePublic literal.pubBytes=some literalPub) :
    FJa_PublicBounds.Bounds (FJa_PublicCopy.native pub) ∧
    SpendDataMap.mapPublic embed (FIw_PublicModel.ofPublic (PIN2W11_PublicCopy.nativePIN2 pub))=
      SpendDataMap.mapPublic ExactBaseProjection.embed literalPub := by
  subst pub
  have bounds:=FJa_PublicBounds.from_raw s (ActualPublicFieldBounds.public_transcript_fields_canonical
    (PIN2W7_TranscriptCopy.digest D) s hash root (PIN2W7_TranscriptCopy.transcript t0) init)
  obtain ⟨bytes,wire,old,mapped,parse,new⟩:=PreparationBinding.decoder_helper_parsePublic
    (PIN2W7_TranscriptCopy.digest D) physical s hash root (PIN2W7_TranscriptCopy.transcript t0) decoded init
  have oldCall : AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
      (AspisR1TerminalDecoder.PublicBinding.toSerializer s)=ok (.Ok encoded) := by
    rw [←PreparationBinding.projection_eq]
    exact serialized
  have eq:=core.result.Result.Ok.inj (Result.ok.inj (old.symm.trans oldCall))
  subst bytes
  exact ⟨bounds,FJq_SourceLiteralPublic.value s encoded wire mapped parse literal.pubBytes literalPub bytesSame parsed⟩
#print axioms value
end AspisR1.FJt_PublicJoin
end
