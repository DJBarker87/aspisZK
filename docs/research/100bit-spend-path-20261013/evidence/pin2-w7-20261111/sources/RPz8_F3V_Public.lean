import RPz8_F3V_PublicModel
import RPz7_F3J_InputRows
import RPz7_PAln_Public
/-! PIN2 W7 (2026-11-11): restated on the PIN2 public bytes.  The selector
facts (`semantic_public`, `toRetainedPublic`) are unchanged at PIN2.  The
premise `init` is now the PIN2 `public_transcript` (Stream C's
`PIN2_NEWGATE_r1_semantic`) of W3c's field copy `PreparationBinding.toPIN2`,
with `D` and `t0` carried by the field copies of `PIN2W7_TranscriptCopy`; the
binder types of `D` and `t0` are unchanged.  In the conclusion only the
`public_bytes` conjunct changes: it now names the PIN2 `public_bytes` of the
`toPIN2` copy; the `parsePublic` and `SemanticTranscript.new` conjuncts are
textually unchanged (the latter is the frozen `new`, which
`PIN2W7_TranscriptCopy.new_eq` shows agrees with the PIN2 one).
The `LiteralTranscript.Public` conjuncts are textually unchanged; the length
fact is the PIN2 `parsed_init_fits` (75 + length <= 1599 <= L = 131072). -/
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.F3V_Public
open AspisR1PublicPreparation AspisR1CurrentCaller
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open MultiproofConeCanonical

theorem from_decode {F C : Type} (c : DrvC_Installation.Configuration F C)
    (physical : Slice U8) (statement : AdapterRw.Cuts.Statement) (semantic : Port1_Driver.Semantic)
    (decodedCall : (DrvC_Installation.sdk c).op47 physical=ok (.Ok statement))
    (selected : AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
      statement=ok semantic)
    (D : AspisR1PublicPreparation.aspis_core.Digest32 Unit) (root : Array U8 32#usize)
    (t0 : AspisR1PublicPreparation.r1_wire.SemanticTranscript Unit)
    (init : AspisR1PublicPreparationPIN2.r1_semantic.public_transcript (PIN2W7_TranscriptCopy.digest D)
      (PreparationBinding.toPIN2
        (FirstComposition.toRetainedPublic (AspisS6CurrentVerifierCarrier.toPublic semantic))) () root=ok (.Ok (PIN2W7_TranscriptCopy.transcript t0))) :
    ∃ (pub : LiteralTranscript.Public) (encoded : alloc.vec.Vec U8),
      AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
        (PreparationBinding.toPIN2
          (FirstComposition.toRetainedPublic (AspisS6CurrentVerifierCarrier.toPublic semantic)))=ok (.Ok encoded) ∧
      pub.pubBytes=bytesOf encoded.val ∧ pub.tag=2 ∧
      (∃ decoded, SemanticPublicWire.parsePublic pub.pubBytes=some decoded) ∧
      AspisR1PublicPreparation.r1_wire.SemanticTranscript.new D () (alloc.vec.Vec.deref encoded) root=ok (.Ok t0) := by
  obtain ⟨encoded,decoded,serialized,parsed,new⟩ := F3V_PublicModel.from_decode c physical statement semantic
    decodedCall selected D root t0 init
  let pub : LiteralTranscript.Public := ⟨bytesOf encoded.val,
    (SemanticPublicCodecComplete.parsed_init_fits _ _ parsed).trans
      (by unfold SelectedTranscriptParams.L; omega),2⟩
  exact ⟨pub,encoded,serialized,rfl,rfl,⟨decoded,parsed⟩,new⟩

#print axioms from_decode
end AspisR1.F3V_Public
end
