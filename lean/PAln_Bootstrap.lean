import PAln_Public
import PAln_Physical
import PAln_Carrier
import PSem_TypedPrefix
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.PAln_Bootstrap
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared
open AspisS1ValuesOwnedInstallation OriginalSerializerInstallation
open MultiproofConeCanonical OraclePortCompactDraft OraclePortStoredDecisionDraftC4
open AspisR1PublicPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge

theorem on_run {CoreError : Type} (adapterOps : AdapterRw.Ops) (ops : Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (B : FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts) (saved : alloc.vec.Vec U8)
    (f : S2W_NativeConsolidation.FirstCut) (s : S2W_NativeConsolidation.SecondCut)
    (cuts : S2W_NativeConsolidation.SourceCuts
      (ClaimsUnrolledSdk.sdkOps adapterOps (Tx1Q_SameCut.dictionary ops reserved query geo) B std)
      accounts1 accounts2 saved f s)
    (selection : AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
      f.statement=ok f.semantic)
    (run : Tx1Q_Execution.Run (Tx1Q_Execution.actual ops reserved query geo B std)
      reserved query geo (Tx1Q_SameCut.callerDigest adapterOps ops reserved query geo B std) ()
      (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved)
    (header : OraclePortHeader.accepts (bytesOf f.proof.val)=true)
    (scan : scan (bytesOf f.proof.val)) :
    ∃ (expanded : Slice U8) (pre : AspisR1PublicPreparation.r1_wire.Prefix)
      (t0 t25 : AspisR1PublicPreparation.r1_wire.SemanticTranscript Unit)
      (cs : List (SourceFull25.Call (retainedDigest
        (Tx1Q_SameCut.callerDigest adapterOps ops reserved query geo B std)) pre))
      (pub : LiteralTranscript.Public),
      ∃ rows : semanticRows 27 0 (slice (bytesOf f.proof.val) 48 6983)=some (pre.records.val.map (fun s => bytesOf s.val)),
      PrefixAdapter.parseAccepted expanded=ok (.Ok pre) ∧
      AspisR1PublicPreparation.r1_semantic.public_transcript (retainedDigest (Tx1Q_SameCut.callerDigest adapterOps ops reserved query geo B std))
        (FirstComposition.toRetainedPublic (AspisS6CurrentVerifierCarrier.toPublic f.semantic)) () pre.c1_root=ok (.Ok t0) ∧
      SourceFull25.Trace (retainedDigest (Tx1Q_SameCut.callerDigest adapterOps ops reserved query geo B std)) pre t0 t25 cs ∧
      cs.map (fun c => c.row.val)=List.range 25 ∧ pub.tag=2 ∧
      (∃ encoded, pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
        (FirstComposition.toRetainedPublic (AspisS6CurrentVerifierCarrier.toPublic f.semantic))=ok (.Ok encoded) ∧
        pub.pubBytes=bytesOf encoded.val) ∧
      ∀ (values : Fin 6 → LiteralTranscript.E) (states : Fin 8 → State)
        (queries : List Nat) (rho : LiteralTranscript.E) (q : Fin 22 → Fin 262144),
        let parsed : Parsed := ⟨bytesOf f.proof.val,pre.records.val.map (fun s => bytesOf s.val)⟩
        let tr := PAln_Carrier.make parsed rows header pub (decodeState pre.c1_root) cs values states queries rho
        Aligned parsed tr ∧ OraclePortStoredParserC4.parseReached parsed.wire tr=some parsed ∧
          ∃ data,LiteralMatchingData.read (typedRows parsed q tr)=some data := by
  obtain ⟨expanded,view,sem,retained,rs,pre,t0,t25,cs,parsed,rows,init,rootPhysical,same,
    opening,out,scratch,trace,order,frames,circles⟩ := PAln_SourceRun.on_run ops reserved query geo B std
      (Tx1Q_SameCut.callerDigest adapterOps ops reserved query geo B std) ()
      (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved run
  obtain ⟨encoded,decoded,serialized,publicParsed,new⟩ := PAln_Public.from_cut
    adapterOps ops reserved query geo B std accounts1 accounts2 saved f s cuts selection
    (retainedDigest (Tx1Q_SameCut.callerDigest adapterOps ops reserved query geo B std)) pre.c1_root t0 init
  let pub : LiteralTranscript.Public := ⟨bytesOf encoded.val,
    (SemanticPublicCodecComplete.parsed_init_fits _ _ publicParsed).trans (by unfold SelectedTranscriptParams.L; omega),2⟩
  have count : cs.length=25 := by
    have h := congrArg List.length order
    simpa only [List.length_map,List.length_range] using h
  have root : bytes (decodeState pre.c1_root)=root0 ⟨bytesOf f.proof.val,pre.records.val.map (fun s => bytesOf s.val)⟩ := by
    rw [PAln_Physical.state_bytes,rootPhysical]
    simp only [PAln_SourceRun.storedRoot,bytesOf,List.map_take,List.map_drop,root0,slice]
  obtain ⟨values,full,encodedPrefix,typed⟩ := PSem_TypedPrefix.typed_prefix expanded pre parsed
  have complete : PSem_TypedPrefix.completedRecords pre=(pre.records.val.map (fun s => bytesOf s.val)).take 25 := by
    simp only [PSem_TypedPrefix.completedRecords,List.map_take]
    rfl
  rw [complete] at typed
  refine ⟨expanded,pre,t0,t25,cs,pub,rows,parsed,init,trace,order,rfl,⟨encoded,serialized,rfl⟩,?_⟩
  intro values states queries rho q
  dsimp only
  apply PAln_Carrier.parser_and_data _ rows header scan ⟨_,typed⟩ pub _ cs count values states queries rho q
  · have tag := ((OraclePortHeader.accepts_iff _).mp header).2.2.1
    simp only [pub,tag,Option.getD_some]
  · exact ⟨decoded,publicParsed⟩
  · exact root

#print axioms on_run
end AspisR1.PAln_Bootstrap
end
