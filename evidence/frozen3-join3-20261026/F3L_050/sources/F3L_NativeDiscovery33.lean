import F3L_PreparedDiscovery
import PAln_Oracle
import RawJ_RecordCuts
import Uni_Cuts
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.F3L_NativeDiscovery33
open AspisR1CurrentCaller InstalledPreparation AspisR1PublicPreparation BorrowedClaimPrepared
open AspisV8R19.MemoizedProgramLaw
open AspisR1PublicPreparation.SourceGlobalOracleInitial AspisR1PublicPreparation.SourceDigestLog
open AspisR1PublicPreparation.PreparedHashCode
open S2W_NativeConsolidation MultiproofConeCanonical OraclePortCompactDraft
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge

theorem native {CoreError : Type} (adapter : AdapterRw.Ops) (ops : Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (B : FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (ClaimsUnrolledSdk.sdkOps adapter (Uni_Install.current ops reserved query geo) B std) native1 native2 hashv)
    (id : S2W_ExtractionBoundary.Program) (accounts1 accounts2 : S2W_ExtractionBoundary.Accounts)
    (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot) (saved : alloc.vec.Vec U8)
    (accepted1 : native1 id accounts1 data1=ok (.Ok saved))
    (accepted2 : native2 id accounts2 data2 slot=ok (.Ok ()))
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (w : CanonicalCutEnrichedTranscript.Words) :
    ∃ f s log,
      SourceCuts (ClaimsUnrolledSdk.sdkOps adapter (Uni_Install.current ops reserved query geo) B std)
        accounts1 accounts2 saved f s ∧
      RawJ_RecordCuts.Recorded f s saved log ∧
      S2W_Trace.run (ClaimsUnrolledSdk.sdkOps adapter (Uni_Install.current ops reserved query geo) B std)
        (S2W_Observation.two (ClaimsUnrolledSdk.sdkOps adapter (Uni_Install.current ops reserved query geo) B std)
          id accounts1 data1 accounts2 data2 slot) []=ok (.Ok saved,log) ∧
    ∃ (i : F3_Model.Input) (pre : r1_wire.Prefix)
      (t0 t25 t26 t27 : AspisR1PublicPreparation.r1_wire.SemanticTranscript Unit)
      (r25 r26 : AspisR1PublicPreparation.r1_wire.ValidatedRecord)
      (z0 z1 : AspisR1PublicPreparation.aspis_core.circle.SecureCirclePoint)
      (start : AspisR1PublicPreparation.transcript.Transcript Unit)
      (cs : List (SourceFull25.Call (retainedDigest (Tx1Q_SameCut.callerDigest adapter (Op5T_Concrete.current ops) reserved query geo B std)) pre))
      (init : PublicInitCall (retainedDigest (Tx1Q_SameCut.callerDigest adapter (Op5T_Concrete.current ops) reserved query geo B std))
        (FirstComposition.toRetainedPublic (AspisS6CurrentVerifierCarrier.toPublic f.semantic)) pre.c1_root t0)
      (v : AspisR1CurrentCaller.verifier.View)
      (c : F3K_OpeningCalls.Calls
        (retainedDigest (Tx1Q_SameCut.callerDigest adapter (Op5T_Concrete.current ops) reserved query geo B std))
        closedHashBoundaries.sampling AspisS1M31Embedding.Total.embed (retainedView v)
        ⟨bytesOf f.proof.val,pre.records.val.map (fun s=>bytesOf s.val)⟩),
      c.t0=start ∧
      i.physical.bytes=bytesOf f.pub.val ∧ i.stored=bytesOf f.proof.val ∧
      i.semantic.value.pubBytes=bytesOf init.encoded.val ∧ i.semantic.value.tag=2 ∧
      SourceFull25.Trace _ pre t0 t25 cs ∧ cs.map (fun c => c.row.val)=List.range 25 ∧
      (∀ row,row<33 → LiteralTranscript.valid row (i.proof row)) ∧
      r1_wire.Prefix.validated_record pre 25#u8=ok (.Ok r25) ∧
      FinishModel.circle_validated (S1SemanticRootCopy.install (ClaimsUnrolledFinish.install std B))
        (retainedDigest (Tx1Q_SameCut.callerDigest adapter (Op5T_Concrete.current ops) reserved query geo B std)) t25 r25=ok (.Ok z0,t26) ∧
      r1_wire.Prefix.validated_record pre 26#u8=ok (.Ok r26) ∧
      FinishModel.circle_validated (S1SemanticRootCopy.install (ClaimsUnrolledFinish.install std B))
        (retainedDigest (Tx1Q_SameCut.callerDigest adapter (Op5T_Concrete.current ops) reserved query geo B std)) t26 r26=ok (.Ok z1,t27) ∧
      AspisR1PublicPreparation.transcript.Transcript.new
        (retainedDigest (Tx1Q_SameCut.callerDigest adapter (Op5T_Concrete.current ops) reserved query geo B std)) () t27.state .S2=ok start ∧
      (eval H (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).1=
        (initPair init::sourceLog cs)++
        (observe (PreparedHashCode.run (S1SemanticCode.circleValidated (S1SemanticRootCopy.install (ClaimsUnrolledFinish.install std B))
          (retainedDigest (Tx1Q_SameCut.callerDigest adapter (Op5T_Concrete.current ops) reserved query geo B std)) t25 r25)).1 ++
        (observe (PreparedHashCode.run (S1SemanticCode.circleValidated (S1SemanticRootCopy.install (ClaimsUnrolledFinish.install std B))
          (retainedDigest (Tx1Q_SameCut.callerDigest adapter (Op5T_Concrete.current ops) reserved query geo B std)) t26 r26)).1 ++
        observe (PreparedHashCode.run (PreparedHashEffects.new effects
          (retainedDigest (Tx1Q_SameCut.callerDigest adapter (Op5T_Concrete.current ops) reserved query geo B std)) () t27.state .S2)).1) ++ F3K_OpeningCalls.log c) ∧
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
  obtain ⟨f,s,log,cuts,recorded,ran⟩ := RawJ_RecordCuts.native _ native1 native2 hashv extraction
    id accounts1 accounts2 data1 data2 slot saved accepted1 accepted2
  have canonical := (Uni_Cuts.scan adapter ops reserved query geo B std accounts1 accounts2 saved f s cuts).2.2
  have shape := Op3I_Cuts.same_cut_header adapter
    (Op5T_Concrete.current (Uni_Install.base ops reserved query geo)) B std
    accounts1 accounts2 saved f s cuts
  have header := shape.2.2.1
  have length : f.proof.val.length=57607 := by
    simpa only [bytesOf,List.length_map] using ((OraclePortHeader.accepts_iff _).mp header).1
  obtain ⟨run,properties⟩ := Uni_Cuts.tx1 adapter ops reserved query geo B std
    accounts1 accounts2 saved f s cuts length
  have inputCuts : SourceCuts (ClaimsUnrolledSdk.sdkOps adapter
      (Tx1Q_SameCut.dictionary (Op5T_Concrete.current ops) reserved query geo) B std)
      accounts1 accounts2 saved f s := by simpa only [Uni_Install.compose_tx1] using cuts
  have extracted : S2W_DigestExtraction.AeneasExtraction
      (ClaimsUnrolledSdk.sdkOps adapter (Tx1Q_SameCut.dictionary (Op5T_Concrete.current ops) reserved query geo) B std)
      native1 native2 hashv := by simpa only [Uni_Install.compose_tx1] using extraction
  have backend := PAln_Oracle.installed_backend adapter (Op5T_Concrete.current ops) reserved query geo B std
    native1 native2 hashv extracted sha256 H p1 syscall
  exact ⟨f,s,log,cuts,recorded,ran,F3L_PreparedDiscovery.from_cut adapter (Op5T_Concrete.current ops)
    reserved query geo B std accounts1 accounts2 saved f s inputCuts recorded.1 run header H backend w canonical⟩

#print axioms native
end AspisR1.F3L_NativeDiscovery33
end
