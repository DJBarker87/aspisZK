import PIN2W7_TranscriptCopy
import RPz7_PAln_SelectedAccepted
import RPz7_RawSourceGlobalOracleInitial
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
The serializer success is `PIN2W7_TranscriptCopy.public_transcript_split`
(W3b's `PIN2_NHG_PublicCarrier.same_execution` plus `new_eq`). -/
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.PAln_Public
open AspisR1PublicPreparation
open AspisR1CurrentCaller
open MultiproofConeCanonical

theorem from_cut {CoreError : Type} (adapterOps : AdapterRw.Ops) (ops : Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (B : FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (saved : alloc.vec.Vec U8)
    (f : S2W_NativeConsolidation.FirstCut) (s : S2W_NativeConsolidation.SecondCut)
    (cuts : S2W_NativeConsolidation.SourceCuts
      (ClaimsUnrolledSdk.sdkOps adapterOps (Tx1Q_SameCut.dictionary ops reserved query geo) B std)
      accounts1 accounts2 saved f s)
    (selection : AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
      f.statement=ok f.semantic)
    (D : AspisR1PublicPreparation.aspis_core.Digest32 Unit) (root : Array U8 32#usize)
    (t0 : AspisR1PublicPreparation.r1_wire.SemanticTranscript Unit)
    (init : AspisR1PublicPreparationPIN2.r1_semantic.public_transcript (PIN2W7_TranscriptCopy.digest D)
      (PreparationBinding.toPIN2
        (FirstComposition.toRetainedPublic (AspisS6CurrentVerifierCarrier.toPublic f.semantic))) () root=ok (.Ok (PIN2W7_TranscriptCopy.transcript t0))) :
    ∃ encoded decoded,
      AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
        (PreparationBinding.toPIN2
          (FirstComposition.toRetainedPublic (AspisS6CurrentVerifierCarrier.toPublic f.semantic)))=ok (.Ok encoded) ∧
      SemanticPublicWire.parsePublic (bytesOf encoded.val)=some decoded ∧
      AspisR1PublicPreparation.r1_wire.SemanticTranscript.new D () (alloc.vec.Vec.deref encoded) root=ok (.Ok t0) := by
  have decoded := AspisS6CurrentCodecInstallation.decode_success f.pub f.statement cuts.decode
  have selected := AspisS6CurrentFirstInstallation.selected_public f.statement
  rw [selection,bind_tc_ok] at selected
  have pubEq := congrArg FirstComposition.toRetainedPublic (Result.ok.inj selected)
  rw [FirstComposition.retained_current_roundtrip] at pubEq
  rw [pubEq] at init ⊢
  obtain ⟨encoded,serialized,new⟩ := PIN2W7_TranscriptCopy.public_transcript_split D _ () root t0 init
  obtain ⟨old,wire,serializedOld,wireSource,parsed,newOld⟩ :=
    PreparationBinding.decoder_helper_parsePublic (PIN2W7_TranscriptCopy.digest D) f.pub
      (AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalStatementV1 f.statement)
      () root (PIN2W7_TranscriptCopy.transcript t0) decoded init
  have oldCall : AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
      (AspisR1TerminalDecoder.PublicBinding.toSerializer
        (AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalStatementV1 f.statement))=ok (.Ok encoded) := by
    rw [← PreparationBinding.projection_eq]
    exact serialized
  have eq : old=encoded := core.result.Result.Ok.inj (Result.ok.inj (serializedOld.symm.trans oldCall))
  subst old
  exact ⟨encoded,_,serialized,parsed,new⟩

#print axioms from_cut
end AspisR1.PAln_Public
end
