import F3L_ModelRead
import PSem_TypedPrefix
import F3L_OpeningFields
import F3K_OpeningQuery
import F3K_OpeningFromSource
import F3K_OpeningSuffix
import F3J_NativeInput
import F3J_First27
import PAln_JoinedRun
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.F3L_PreparedDiscovery
open AspisR1CurrentCaller InstalledPreparation AspisR1PublicPreparation
open BorrowedClaimPrepared AspisS1ValuesOwnedInstallation OriginalSerializerInstallation
open AspisR1PublicPreparation.PreparedHashCode
open MultiproofConeCanonical OraclePortCompactDraft SourceGlobalOracleInitial SourceDigestLog
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw
attribute [local irreducible] F3J_InputRows.proof F3J_SamplerRun.program

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
    (w : CanonicalCutEnrichedTranscript.Words)
    (canonical : scan (bytesOf f.proof.val)) :
    ∃ (i : F3_Model.Input) (pre : r1_wire.Prefix)
      (t0 t25 t26 t27 : AspisR1PublicPreparation.r1_wire.SemanticTranscript Unit)
      (r25 r26 : AspisR1PublicPreparation.r1_wire.ValidatedRecord)
      (z0 z1 : AspisR1PublicPreparation.aspis_core.circle.SecureCirclePoint)
      (start : AspisR1PublicPreparation.transcript.Transcript Unit)
      (cs : List (SourceFull25.Call (retainedDigest (Tx1Q_SameCut.callerDigest adapter ops reserved query geo B std)) pre))
      (init : PublicInitCall (retainedDigest (Tx1Q_SameCut.callerDigest adapter ops reserved query geo B std))
        (FirstComposition.toRetainedPublic (AspisS6CurrentVerifierCarrier.toPublic f.semantic)) pre.c1_root t0)
      (v : AspisR1CurrentCaller.verifier.View)
      (c : F3K_OpeningCalls.Calls
        (retainedDigest (Tx1Q_SameCut.callerDigest adapter ops reserved query geo B std))
        closedHashBoundaries.sampling AspisS1M31Embedding.Total.embed (retainedView v)
        ⟨bytesOf f.proof.val,pre.records.val.map (fun s=>bytesOf s.val)⟩),
      c.t0=start ∧
      i.physical.bytes=bytesOf f.pub.val ∧ i.stored=bytesOf f.proof.val ∧
      i.semantic.value.pubBytes=bytesOf init.encoded.val ∧ i.semantic.value.tag=2 ∧
      SourceFull25.Trace _ pre t0 t25 cs ∧ cs.map (fun c => c.row.val)=List.range 25 ∧
      (∀ row,row<33 → LiteralTranscript.valid row (i.proof row)) ∧
      r1_wire.Prefix.validated_record pre 25#u8=ok (.Ok r25) ∧
      FinishModel.circle_validated (S1SemanticRootCopy.install (ClaimsUnrolledFinish.install std B))
        (retainedDigest (Tx1Q_SameCut.callerDigest adapter ops reserved query geo B std)) t25 r25=ok (.Ok z0,t26) ∧
      r1_wire.Prefix.validated_record pre 26#u8=ok (.Ok r26) ∧
      FinishModel.circle_validated (S1SemanticRootCopy.install (ClaimsUnrolledFinish.install std B))
        (retainedDigest (Tx1Q_SameCut.callerDigest adapter ops reserved query geo B std)) t26 r26=ok (.Ok z1,t27) ∧
      AspisR1PublicPreparation.transcript.Transcript.new
        (retainedDigest (Tx1Q_SameCut.callerDigest adapter ops reserved query geo B std)) () t27.state .S2=ok start ∧
      (eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).1=
        (initPair init::sourceLog cs)++
        (observe (PreparedHashCode.run (S1SemanticCode.circleValidated (S1SemanticRootCopy.install (ClaimsUnrolledFinish.install std B))
          (retainedDigest (Tx1Q_SameCut.callerDigest adapter ops reserved query geo B std)) t25 r25)).1 ++
        (observe (PreparedHashCode.run (S1SemanticCode.circleValidated (S1SemanticRootCopy.install (ClaimsUnrolledFinish.install std B))
          (retainedDigest (Tx1Q_SameCut.callerDigest adapter ops reserved query geo B std)) t26 r26)).1 ++
        observe (PreparedHashCode.run (PreparedHashEffects.new effects
          (retainedDigest (Tx1Q_SameCut.callerDigest adapter ops reserved query geo B std)) () t27.state .S2)).1) ++ F3K_OpeningCalls.log c) ∧
      UnifiedSampler.stateOf SelectedTranscriptParams.params
        (LiteralTranscript.erasePrefix (eval H
          (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2)=decodeState c.t6.state ∧
      (∃ j,D0InstanceAdmission.Fields (LiteralTranscript.erasePrefix (eval H
        (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2) j) ∧
      ∃ q,OraclePortSelectedDraft.queries (LiteralTranscript.erasePrefix (eval H
        (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2)=some q ∧
        (∀ j : Fin 22,(c.queries.val[j.val]'(by have len : c.queries.val.length=22:=c.queries.property;omega)).val=(q j).val) ∧
        OraclePortStoredParserC4.parseReached i.stored (LiteralTranscript.erasePrefix (eval H
          (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2)=
            some ⟨bytesOf f.proof.val,pre.records.val.map (fun s=>bytesOf s.val)⟩ ∧
        ∃ sourceInput,OraclePortStoredDecisionDraftC4.input
          ⟨bytesOf f.proof.val,pre.records.val.map (fun s=>bytesOf s.val)⟩ q
          (LiteralTranscript.erasePrefix (eval H (F3J_SamplerRun.program i.proof 0 33
            (FS.emptyPrefix i.semantic.value))).2)=some sourceInput := by
  obtain ⟨expanded,y1,view,sem,retained,rs,pre,t0,t25,cs,parsed,rows,publicInit,rootPhysical,wide,same,
    y1Frame,round0Frame,round1Frame,finalFrame,secondFrame,opening,out,scratch,trace,order,frames,circles⟩ := PAln_JoinedRun.on_run ops reserved query geo B std
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
  obtain ⟨r25,r26,z0,t26,z1,t27,read25,call25,read26,call26,trEq⟩ := circles
  have variant := sourceView_variant f.proof expanded y1 view wide
  have retainedVariant : (retainedView view).variant=AspisR1PublicPreparation.transport.Variant.S2 := by
    change InstalledPreparation.retainedVariant view.variant=_
    rw [variant]
    rfl
  obtain ⟨c,seed,claim,outputEq,powerEq,claimEq⟩ := F3K_OpeningFromSource.from_double
    (retainedDigest (Tx1Q_SameCut.callerDigest adapter ops reserved query geo B std))
    f.proof expanded y1 view wide p rfl y1Frame (retainedSem sem) () retained rs opening
  rw [trEq,retainedVariant] at seed
  let start := c.t0
  have exactPrefix := F3J_First27.sampler trace count init
    (S1SemanticRootCopy.install (ClaimsUnrolledFinish.install std B)) r25 r26 t26 t27 z0 z1
    read25 call25 read26 call26 () start seed H backend p rows rfl w bound (FS.emptyPrefix pub) tag pubInit
  let P27 := (eval H (F3J_SamplerRun.program i.proof 0 27 (FS.emptyPrefix pub))).2
  have suffix := F3K_OpeningSuffix.sampler c H backend (decodeState pre.c1_root) w bound P27 exactPrefix.2
  have logs := F3J_SamplerCompose.logs H i.proof 0 27 6 (FS.emptyPrefix pub)
  have values := F3J_SamplerCompose.value H i.proof 0 27 6 (FS.emptyPrefix pub)
  have len : P27.rounds.length=27 := F3J_SamplerRun.length H i.proof 0 27 (FS.emptyPrefix pub)
  obtain ⟨q,selectedQ,coordinates⟩ := F3K_OpeningQuery.decoded c H backend (decodeState pre.c1_root)
    w bound P27 len exactPrefix.2
  have rootBytes : bytes (decodeState pre.c1_root)=root0 p := by
    rw [PAln_Physical.state_bytes,rootPhysical]
    simp only [PAln_JoinedRun.storedRoot,bytesOf,List.map_take,List.map_drop,root0,slice,p]
  obtain ⟨typedValues,full,encodedPrefix,typed⟩ := PSem_TypedPrefix.typed_prefix expanded pre parsed
  have complete : PSem_TypedPrefix.completedRecords pre=p.semantic.take 25 := by
    simp only [PSem_TypedPrefix.completedRecords,List.map_take,p]
    rfl
  rw [complete] at typed
  have tagWire : pub.tag=p.wire[8]?.getD 0 := by
    have h := ((OraclePortHeader.accepts_iff _).mp header).2.2.1
    rw [tag]
    simp only [p,h,Option.getD_some]
  have modelRead := F3L_ModelRead.read H p (decodeState pre.c1_root) w bound pub q rows header
    canonical ⟨typedValues,typed⟩ tagWire publicParsed rootBytes
  obtain ⟨metadata,dataRead⟩ := modelRead.2.2
  refine ⟨i,pre,t0,t25,t26,t27,r25,r26,z0,z1,start,cs,init,view,c,rfl,rfl,rfl,by rw [encoding];exact pubEq,
    tag,trace,order,F3J_InputRows.valid p _ w bound,read25,call25,read26,call26,seed,?_,?_,?_,?_⟩
  · change (eval H (F3J_SamplerRun.program i.proof 0 (27+6) (FS.emptyPrefix pub))).1=_
    exact (logs.trans (congrArg₂ List.append exactPrefix.1 suffix.1)).trans (List.append_assoc _ _ _)
  · change UnifiedSampler.stateOf SelectedTranscriptParams.params
      (LiteralTranscript.erasePrefix (eval H (F3J_SamplerRun.program i.proof 0 (27+6) (FS.emptyPrefix pub))).2)=_
    exact (congrArg (fun Q=>UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix Q)) values).trans suffix.2

  · have len : P27.rounds.length=27 := F3J_SamplerRun.length H i.proof 0 27 (FS.emptyPrefix pub)
    have parsedP : ∃ decoded,SemanticPublicWire.parsePublic P27.statement.pubBytes=some decoded := by
      rw [F3L_SamplerStatement.statement]
      exact publicParsed
    have hfields := F3L_OpeningFields.fields c H backend (decodeState pre.c1_root)
      w bound P27 len parsedP metadata exactPrefix.2
    change ∃ j,D0InstanceAdmission.Fields (LiteralTranscript.erasePrefix (eval H
      (F3J_SamplerRun.program i.proof 0 (27+6) (FS.emptyPrefix pub))).2) j
    rw [values]
    exact hfields
  · have parsedP : ∃ decoded,SemanticPublicWire.parsePublic P27.statement.pubBytes=some decoded := by
      rw [F3L_SamplerStatement.statement]
      exact publicParsed
    have hfields := F3L_OpeningFields.fields c H backend (decodeState pre.c1_root)
      w bound P27 len parsedP metadata exactPrefix.2
    have fields33 : ∃ j,D0InstanceAdmission.Fields (LiteralTranscript.erasePrefix (eval H
      (F3J_SamplerRun.program i.proof 0 (27+6) (FS.emptyPrefix pub))).2) j := by
      rw [values]
      exact hfields
    have existsInput := (F3L_InputDiscovery.exists_input p q _).mpr ⟨fields33,⟨metadata,dataRead⟩⟩
    exact ⟨q,(congrArg (fun Q=>OraclePortSelectedDraft.queries (LiteralTranscript.erasePrefix Q)) values).trans selectedQ,
      coordinates,modelRead.2.1,existsInput⟩

#print axioms from_cut
end AspisR1.F3L_PreparedDiscovery
end
