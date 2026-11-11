import RPz7_F3J_InputRows
import RPz7_PAln_Public
/-! PIN2 W7 (2026-11-11): restated on the PIN2 public transcript, following
the restated `RPz7_PAln_Public.from_cut`.  `D`, `t0`, `init` and the `public_bytes` and
`SemanticTranscript.new` conjuncts are retargeted to the PIN2 carrier through
W3c's field copy `PreparationBinding.toPIN2`; the `LiteralTranscript.Public`
conjuncts are textually unchanged; the length fact is the PIN2
`parsed_init_fits` (75 + length <= 1599 <= L). -/
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.F3J_Public
open AspisR1PublicPreparation AspisR1CurrentCaller
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open MultiproofConeCanonical

theorem from_cut {CoreError : Type} (adapter : AdapterRw.Ops) (ops : Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (B : FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (saved : alloc.vec.Vec U8)
    (f : S2W_NativeConsolidation.FirstCut) (s : S2W_NativeConsolidation.SecondCut)
    (cuts : S2W_NativeConsolidation.SourceCuts
      (ClaimsUnrolledSdk.sdkOps adapter (Tx1Q_SameCut.dictionary ops reserved query geo) B std)
      accounts1 accounts2 saved f s)
    (selected : AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
      f.statement = ok f.semantic)
    (D : AspisR1PublicPreparationPIN2.aspis_core.digest.Digest32 Unit) (root : Array U8 32#usize)
    (t0 : AspisR1PublicPreparationPIN2.r1_wire.SemanticTranscript Unit)
    (init : AspisR1PublicPreparationPIN2.r1_semantic.public_transcript D
      (PreparationBinding.toPIN2
        (FirstComposition.toRetainedPublic (AspisS6CurrentVerifierCarrier.toPublic f.semantic))) () root=ok (.Ok t0)) :
    ∃ (pub : LiteralTranscript.Public) (encoded : alloc.vec.Vec U8),
      AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
        (PreparationBinding.toPIN2
          (FirstComposition.toRetainedPublic (AspisS6CurrentVerifierCarrier.toPublic f.semantic)))=ok (.Ok encoded) ∧
      pub.pubBytes=bytesOf encoded.val ∧ pub.tag=2 ∧
      (∃ decoded, SemanticPublicWire.parsePublic pub.pubBytes=some decoded) ∧
      AspisR1PublicPreparationPIN2.r1_wire.SemanticTranscript.new D () (alloc.vec.Vec.deref encoded) root=ok (.Ok t0) := by
  obtain ⟨encoded,decoded,serialized,parsed,new⟩ := PAln_Public.from_cut adapter ops reserved query geo B std
    accounts1 accounts2 saved f s cuts selected D root t0 init
  let pub : LiteralTranscript.Public := ⟨bytesOf encoded.val,
    (SemanticPublicCodecComplete.parsed_init_fits _ _ parsed).trans
      (by unfold SelectedTranscriptParams.L; omega),2⟩
  exact ⟨pub,encoded,serialized,rfl,rfl,⟨decoded,parsed⟩,new⟩

#print axioms from_cut
end AspisR1.F3J_Public
end
