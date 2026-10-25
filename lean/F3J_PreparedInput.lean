import F3J_NativeInput
import F3J_First25
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.F3J_PreparedInput
open AspisR1CurrentCaller InstalledPreparation AspisR1PublicPreparation
open MultiproofConeCanonical OraclePortCompactDraft SourceGlobalOracleInitial SourceDigestLog
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw

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
    (H : Bytes → State)
    (backend : Tx1DigestLog.ByteOracleBackend (retainedDigest (Tx1Q_SameCut.callerDigest adapter ops reserved query geo B std)) H)
    (w : CanonicalCutEnrichedTranscript.Words) :
    ∃ (i : F3_Model.Input) (pre : r1_wire.Prefix)
      (t0 t25 : AspisR1PublicPreparation.r1_wire.SemanticTranscript Unit)
      (cs : List (SourceFull25.Call (retainedDigest (Tx1Q_SameCut.callerDigest adapter ops reserved query geo B std)) pre))
      (init : PublicInitCall (retainedDigest (Tx1Q_SameCut.callerDigest adapter ops reserved query geo B std))
        (FirstComposition.toRetainedPublic (AspisS6CurrentVerifierCarrier.toPublic f.semantic)) pre.c1_root t0),
      i.physical.bytes=bytesOf f.pub.val ∧ i.stored=bytesOf f.proof.val ∧
      i.semantic.value.pubBytes=bytesOf init.encoded.val ∧ i.semantic.value.tag=2 ∧
      SourceFull25.Trace _ pre t0 t25 cs ∧ cs.map (fun c => c.row.val)=List.range 25 ∧
      (∀ row,row<33 → LiteralTranscript.valid row (i.proof row)) ∧
      (eval H (F3J_SamplerRun.program i.proof 0 25 (FS.emptyPrefix i.semantic.value))).1=
        initPair init::sourceLog cs ∧
      UnifiedSampler.stateOf SelectedTranscriptParams.params
        (LiteralTranscript.erasePrefix (eval H
          (F3J_SamplerRun.program i.proof 0 25 (FS.emptyPrefix i.semantic.value))).2)=decodeState t25.state := by
  obtain ⟨expanded,view,sem,retained,rs,pre,t0,t25,cs,parsed,rows,publicInit,rootPhysical,same,
    opening,out,scratch,trace,order,frames,circles⟩ := PAln_SourceRun.on_run ops reserved query geo B std
      (Tx1Q_SameCut.callerDigest adapter ops reserved query geo B std) ()
      (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved run
  obtain ⟨pub,encoded,serialized,pubEq,tag,publicParsed,new⟩ := F3J_Public.from_cut adapter ops reserved query geo B std
    accounts1 accounts2 saved f s cuts selected _ pre.c1_root t0 publicInit
  have initHash : t0.hash=() := Subsingleton.elim _ _
  obtain ⟨init⟩ := public_success_has_init_call _
    (FirstComposition.toRetainedPublic (AspisS6CurrentVerifierCarrier.toPublic f.semantic)) pre.c1_root t0
    (by simpa only [initHash] using publicInit)
  have encoding : init.encoded=encoded := core.result.Result.Ok.inj (Result.ok.inj (init.serialized.symm.trans serialized))
  let p : Parsed := ⟨bytesOf f.proof.val,pre.records.val.map (fun s => bytesOf s.val)⟩
  have bound : ∀ row,(rowBytes p row).length≤SelectedTranscriptParams.D :=
    PAln_RowBounds.row_bound p rows ((OraclePortHeader.accepts_iff _).mp header).1
  let i := F3J_InputRows.input p (decodeState pre.c1_root) w bound pub (bytesOf f.pub.val)
  have count : cs.length=25 := by
    have length := congrArg List.length order
    simpa only [List.length_map,List.length_range] using length
  have pubInit : pub.pubBytes=SourceDigestAddresses.rawBytes (alloc.vec.Vec.deref init.encoded) := by
    rw [encoding,pubEq]
    rfl
  have exactPrefix := F3J_First25.sampler trace count init H backend p rows rfl w bound (FS.emptyPrefix pub) pubInit
  exact ⟨i,pre,t0,t25,cs,init,rfl,rfl,by rw [encoding];exact pubEq,tag,trace,order,
    F3J_InputRows.valid p _ w bound,exactPrefix.1,exactPrefix.2⟩

#print axioms from_cut
end AspisR1.F3J_PreparedInput
end
