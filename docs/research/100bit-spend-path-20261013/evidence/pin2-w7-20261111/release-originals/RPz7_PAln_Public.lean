import RPz7_PAln_SelectedAccepted
import RPz7_RawSourceGlobalOracleInitial
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
    (init : AspisR1PublicPreparation.r1_semantic.public_transcript D
      (FirstComposition.toRetainedPublic (AspisS6CurrentVerifierCarrier.toPublic f.semantic)) () root=ok (.Ok t0)) :
    ∃ encoded decoded,
      AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
        (FirstComposition.toRetainedPublic (AspisS6CurrentVerifierCarrier.toPublic f.semantic))=ok (.Ok encoded) ∧
      SemanticPublicWire.parsePublic (bytesOf encoded.val)=some decoded ∧
      AspisR1PublicPreparation.r1_wire.SemanticTranscript.new D () (alloc.vec.Vec.deref encoded) root=ok (.Ok t0) := by
  have decoded := AspisS6CurrentCodecInstallation.decode_success f.pub f.statement cuts.decode
  have selected := AspisS6CurrentFirstInstallation.selected_public f.statement
  rw [selection,bind_tc_ok] at selected
  have pubEq := congrArg FirstComposition.toRetainedPublic (Result.ok.inj selected)
  rw [FirstComposition.retained_current_roundtrip] at pubEq
  rw [pubEq] at init ⊢
  obtain ⟨encoded,serialized,new⟩ := PreparationSuccess.public_transcript_success D _ () root t0 init
  obtain ⟨old,wire,serializedOld,wireSource,parsed,newOld⟩ :=
    PreparationBinding.decoder_helper_parsePublic D f.pub
      (AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalStatementV1 f.statement)
      () root t0 decoded init
  have oldCall : AspisR1PublicSerializer.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
      (AspisR1TerminalDecoder.PublicBinding.toSerializer
        (AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalStatementV1 f.statement))=ok (.Ok encoded) := by
    rw [← PreparationBinding.projection_eq,SerializerWhole.serializer_eq,serialized]
    rfl
  have eq : old=encoded := core.result.Result.Ok.inj (Result.ok.inj (serializedOld.symm.trans oldCall))
  subst old
  exact ⟨encoded,_,serialized,parsed,new⟩

#print axioms from_cut
end AspisR1.PAln_Public
end
