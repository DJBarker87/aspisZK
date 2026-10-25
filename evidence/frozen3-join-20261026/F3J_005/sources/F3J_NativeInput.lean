import F3J_Public
import PAln_SourceRun
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.F3J_NativeInput
open AspisR1CurrentCaller InstalledPreparation
open AspisR1PublicPreparation
open MultiproofConeCanonical OraclePortCompactDraft
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge

theorem from_cut {CoreError : Type} (adapter : AdapterRw.Ops) (ops : Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (B : FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (saved : alloc.vec.Vec U8)
    (f : S2W_NativeConsolidation.FirstCut) (s : S2W_NativeConsolidation.SecondCut)
    (cuts : S2W_NativeConsolidation.SourceCuts
      (ClaimsUnrolledSdk.sdkOps adapter (Tx1Q_SameCut.dictionary ops reserved query geo) B std)
      accounts1 accounts2 saved f s)
    (selected : AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
      f.statement=ok f.semantic)
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual ops reserved query geo B std)
      reserved query geo (Tx1Q_SameCut.callerDigest adapter ops reserved query geo B std) ()
      (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved)
    (header : OraclePortHeader.accepts (bytesOf f.proof.val)=true)
    (w : CanonicalCutEnrichedTranscript.Words) :
    ∃ (i : F3_Model.Input) (pre : r1_wire.Prefix) (encoded : alloc.vec.Vec U8),
      i.physical.bytes=bytesOf f.pub.val ∧ i.stored=bytesOf f.proof.val ∧
      pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
        (FirstComposition.toRetainedPublic (AspisS6CurrentVerifierCarrier.toPublic f.semantic))=ok (.Ok encoded) ∧
      i.semantic.value.pubBytes=bytesOf encoded.val ∧ i.semantic.value.tag=2 ∧
      (∃ decoded,SemanticPublicWire.parsePublic i.semantic.value.pubBytes=some decoded) ∧
      semanticRows 27 0 (slice i.stored 48 6983)=some (pre.records.val.map (fun s => bytesOf s.val)) ∧
      (∀ row, row<33 → LiteralTranscript.valid row (i.proof row)) ∧
      (∃ bound : ∀ row,(rowBytes ⟨i.stored,pre.records.val.map (fun s => bytesOf s.val)⟩ row).length ≤ SelectedTranscriptParams.D,
        ∀ row,LiteralTranscript.erase (i.proof row)=
          if row=0 then .initial (decodeState pre.c1_root)
          else .payload ⟨rowBytes ⟨i.stored,pre.records.val.map (fun s => bytesOf s.val)⟩ row,bound row⟩) ∧
      bytes (decodeState pre.c1_root)=slice i.stored 16 32 := by
  obtain ⟨expanded,view,sem,retained,rs,pre,t0,t25,cs,parsed,rows,init,rootPhysical,rest⟩ :=
    PAln_SourceRun.on_run ops reserved query geo B std
      (Tx1Q_SameCut.callerDigest adapter ops reserved query geo B std) ()
      (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved run
  obtain ⟨pub,encoded,serialized,pubEq,tag,publicParsed,new⟩ := F3J_Public.from_cut adapter ops reserved query geo B std
    accounts1 accounts2 saved f s cuts selected _ pre.c1_root t0 init
  let p : Parsed := ⟨bytesOf f.proof.val,pre.records.val.map (fun s => bytesOf s.val)⟩
  have bound : ∀ row, (rowBytes p row).length ≤ SelectedTranscriptParams.D :=
    PAln_RowBounds.row_bound p rows ((OraclePortHeader.accepts_iff _).mp header).1
  let i := F3J_InputRows.input p (decodeState pre.c1_root) w bound pub (bytesOf f.pub.val)
  refine ⟨i,pre,encoded,rfl,rfl,serialized,pubEq,tag,publicParsed,rows,?_,?_,?_⟩
  · exact F3J_InputRows.valid p _ w bound
  · exact ⟨bound,F3J_InputRows.erased p _ w bound⟩
  · rw [PAln_Physical.state_bytes,rootPhysical]
    simp only [PAln_SourceRun.storedRoot,bytesOf,List.map_take,List.map_drop,slice]
    rfl

#print axioms from_cut
end AspisR1.F3J_NativeInput
end
