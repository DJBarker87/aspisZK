import Hist_SdkStrong
import WAdm_NativeAccepted
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.Hist_AcceptedStrong
open ClaimsUnrolledSdk
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared
open AspisR1ClaimPreparedBridge AspisR1ClaimPreparedBridge.InstalledMeaning
open AspisR1CurrentPreparedClaim.Concrete OriginalSerializerInstallation
open AspisS1ValuesOwnedInstallation AspisS1NativeBufferClaimTrace
open S2Trust S2LeadInterface S2W_D189Entry S2W_D189Wrappers S2W_TrustedStd
open S2W_WrapperLaws S2W_ReturnedCheckpoint S2W_EntryWriteHistory S2W_CommittedCheckpoint
open S2W_D189Consolidation S2W_NativeConsolidation S2W_AuthenticatedInputs S2W_InputSchedule
open S2W_ExpandedChildren S2W_TraceSplice MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- Same original accepted pair and original conclusions, with the bounded
native certificate input class DERIVED on its own preparation/query/flush and
concrete emitted writer16 substituted on exactly that input, returning the
same saved Vec. Runtime/allocator/syscall and named owner trust are retained.
The native-source link is WAdm_KANI001 plus the checked emitted-source bridge;
no unrestricted all-input native/reference equality is asserted. -/
theorem accepted_pair_claims_tx1 {W A E M Cv CoreError : Type} {N : Nat}
    (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A)
    (e1 e2 : Entry) (w1 w2 : W)
    (admission1 : RuntimeEntrypointAdmission L e1 w1 3)
    (admission2 : RuntimeEntrypointAdmission L e2 w2 7)
    (adapterOps : AdapterRw.Ops) (ops : Ops)
    (reserved : Bool) (queryOps : Port3_NativeQueryBody.Ops)
    (geoOps : Port3_NativeGeometryBody.Ops CoreError)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (claimsStd : ClaimsUnrolledFinish.StdCalls)
    (prepareOwner : WAdm_Domain.SessionAPrepare (Tx1Q_Execution.actual ops reserved queryOps geoOps B claimsStd))
    (primitiveOwner : Port5Q1_QueryPorts.SessionAPrimitives queryOps) (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (sdkOps adapterOps (Tx1Q_SameCut.dictionary ops reserved queryOps geoOps) B claimsStd) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (program : S2W_ExtractionBoundary.Program) (data1 data2 : Slice U8)
    (slot : S2W_ExtractionBoundary.Slot) (state1 state2 final1 final2 : A)
    (saved : alloc.vec.Vec U8) (post1 post2 : Heap (Nat → Record))
    (accepted1 : S2W_D189Wrappers.first native1 copy allocator e1 program data1 state1 =
      ok (.Ok (saved,post1,final1)))
    (accepted2 : S2W_D189Wrappers.second native2 allocator e2 program data2 slot state2 =
      ok (.Ok (post2,final2)))
    (p : FS2.Duplex.Params M Cv N) (root : Array U8 32#usize) (length : U32)
    (port : ChildConeJoin E (sdkOps adapterOps (Tx1Q_SameCut.dictionary ops reserved queryOps geoOps) B claimsStd)) (firstMarks : FirstMarks port) (secondMarks : SecondMarks port) :
    ∃ f s validated outer pre middle fs ss,
      SourceCuts (sdkOps adapterOps (Tx1Q_SameCut.dictionary ops reserved queryOps geoOps) B claimsStd) e1.first (e2.second secondSizes) saved f s ∧
      AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
        f.statement = ok f.semantic ∧
      AdapterRw.r1_pool_adapter.owned.validate_asq8
        (sdkOps adapterOps (Tx1Q_SameCut.dictionary ops reserved queryOps geoOps) B claimsStd)
        program (e2.second secondSizes) data2 slot = ok (.Ok validated) ∧
      (sdkOps adapterOps (Tx1Q_SameCut.dictionary ops reserved queryOps geoOps) B claimsStd).op22
        validated.statement = ok (.Ok s.encoded) ∧
      ((RowShape_InstalledSlots.verifierOps (Tx1Q_SameCut.dictionary ops reserved queryOps geoOps) B claimsStd).op3 f.proof = ok (.Ok .S2) ∧
        Op3I_Install.sourceBody f.proof = ok (.Ok .S2) ∧
        OraclePortHeader.accepts (bytesOf f.proof.val) = true ∧
        Op3I_Cuts.frozenHeader (bytesOf f.proof.val) = some .S2) ∧
      ((RowShape_InstalledSlots.verifierOps (Tx1Q_SameCut.dictionary ops reserved queryOps geoOps) B claimsStd).op4 f.proof = ok (.Ok ()) ∧
        Op4P_Install.sourceBody f.proof = ok (.Ok ()) ∧
        OraclePortCompactDraft.scan (bytesOf f.proof.val)) ∧
      (∃ run : Tx1Q_Execution.Run (Tx1Q_Execution.actual ops reserved queryOps geoOps B claimsStd) reserved queryOps geoOps
      (Tx1Q_SameCut.callerDigest adapterOps ops reserved queryOps geoOps B claimsStd) ()
      (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved,
      reserved = true ∧ f.split = 10#usize ∧ run.out.next.val = 10 ∧ run.flushed.val.length = 64 ∧
      (∀ x ∈ (Tx1Q_Carriers.slice Tx1Q_Carriers.k run.flushed).val, Port3_FlushInstall.Canonical x) ∧
      Port3_CheckpointInstall.writer
        (Tx1Q_Install.digest (Tx1Q_SameCut.callerDigest adapterOps ops reserved queryOps geoOps B claimsStd))
        (Tx1Q_Carriers.prepared run.p)
        (Tx1Q_Carriers.accumulator {run.out with weights := ⟨run.flushed.val,run.flushed.property⟩})
        f.proof f.pub () = ok saved ∧
      WAdm_Domain.Admitted (Tx1Q_Carriers.prepared run.p)
        (Tx1Q_Carriers.accumulator {run.out with weights := ⟨run.flushed.val,run.flushed.property⟩}) f.proof f.pub ∧
      WAdm_Carrier.WideInputs (Tx1Q_Carriers.prepared run.p)
        (Tx1Q_Carriers.accumulator {run.out with weights := ⟨run.flushed.val,run.flushed.property⟩}) ∧
      WAdm_SourceWriter.writer
        (Tx1Q_Install.digest (Tx1Q_SameCut.callerDigest adapterOps ops reserved queryOps geoOps B claimsStd))
        (Tx1Q_Carriers.prepared run.p) (Tx1Q_Carriers.accumulator {run.out with weights := ⟨run.flushed.val,run.flushed.property⟩})
        f.proof f.pub () = ok saved ∧
      (WAdm_NativeInstall.install (Tx1Q_Execution.actual ops reserved queryOps geoOps B claimsStd)).op16
        (Tx1Q_SameCut.callerDigest adapterOps ops reserved queryOps geoOps B claimsStd) run.p
        {run.out with weights := ⟨run.flushed.val,run.flushed.property⟩}
        f.proof f.pub () = ok saved ∧ Tx1Q_Endpoint.WhenBound run) ∧
      S2W_ExpandedTrace.runExpanded (sdkOps adapterOps (Tx1Q_SameCut.dictionary ops reserved queryOps geoOps) B claimsStd) (children port)
        (S2W_Observation.two (sdkOps adapterOps (Tx1Q_SameCut.dictionary ops reserved queryOps geoOps) B claimsStd) program e1.first data1 (e2.second secondSizes) data2 slot) [] =
        ok (.Ok saved,S2W_ExpandedTrace.full (children port) outer) ∧
      S2W_D189Interpretation.runOwned (sdkOps adapterOps (Tx1Q_SameCut.dictionary ops reserved queryOps geoOps) B claimsStd)
        (S2W_Observation.two (sdkOps adapterOps (Tx1Q_SameCut.dictionary ops reserved queryOps geoOps) B claimsStd) program e1.first data1 (e2.second secondSizes) data2 slot) [] e1.heap =
        ok (.Ok saved,outer,e1.heap) ∧
      projected port outer = S2W_SiteSchedule.timeline pre middle fs ss ∧
      post2 = e2.heap ∧
      before e1 e2 .tx1 = S2W_D189Interpretation.nativeObserve L encode e1.metadata 3 w1 e1.heap.ambient ∧
      before e1 e2 .tx2 = S2W_D189Interpretation.nativeObserve L encode e2.metadata 7 w2 e2.heap.ambient ∧
      (∃ selectedPublic,
        AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
          f.statement = ok selectedPublic ∧
        SourceCuts (sdkOps adapterOps (Tx1Q_SameCut.dictionary ops reserved queryOps geoOps) B claimsStd) e1.first (e2.second secondSizes) saved
          {f with semantic := selectedPublic} s ∧
        ∃ (semantic y1 : Slice U8) (v : AspisR1SelectedWideViewV1.verifier.View)
          (sem : r1_semantic.Verified Unit) (claimsPrefix : AspisR1PublicPreparation.r1_wire.Prefix),
          AspisR1SelectedWideViewV1.verifier.candidate.wide_view f.proof semantic y1 = ok (.Ok v) ∧
          (semanticBase (Tx1Q_SameCut.dictionary ops reserved queryOps geoOps) (ClaimsUnrolledFinish.install claimsStd B)).op9
            (NativeBuffers.callerDigest adapterOps (withValues (Tx1Q_SameCut.dictionary ops reserved queryOps geoOps)) nativeValues
              AspisS1ExtractedRoundChildren.children (ClaimsUnrolledFinish.install claimsStd B))
            (FirstComposition.toCurrentPublic
              (AspisR1PublicPreparation.PreparationBinding.preparationPublic
                (AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalStatementV1 f.statement)))
            v.semantic () none = ok (.Ok sem) ∧
          AspisR1PublicPreparation.PrefixAdapter.parseAccepted v.semantic = ok (.Ok claimsPrefix) ∧
          ClaimsUnrolledFinish.reference claimsStd claimsPrefix = ok (.Ok (retainedSem sem).claims)) ∧
      ∀ (decode : HeaderDecode) (nodes : Nat → Nat → Slice U8) (y1 : Slice U8),
      CheckpointWriterConeJoin (sdkOps adapterOps (Tx1Q_SameCut.dictionary ops reserved queryOps geoOps) B claimsStd) decode H f.semantic f.pub f.proof f.split →
      CheckpointReaderConeJoin (sdkOps adapterOps (Tx1Q_SameCut.dictionary ops reserved queryOps geoOps) B claimsStd) decode H s.pub s.proof s.checkpoint →
      S2X.CheckpointVersionBinding
        (payloadBytes encode (post1.payload (e1.heap.accounts 2).1) 1768) (bytesOf s.checkpoint.val) →
      P2Prime H f.proof f.pub s.proof s.pub →
      S2W_ChildJoins.FirstEntryVerifierConeJoin f.proof →
      S2W_ChildJoins.MultiproofConeJoin f.proof s.proof nodes →
      S2W_ChildJoins.S8StageConeJoin f.proof y1 →
      ∃ parsed,
        S2W_LeadInterface.S2CallerFacts
          (observation f s saved nodes y1 pre middle fs ss (before e1 e2) (after e1 e2 post1))
          (S2Z.Oracle.leadDigest (sdkOps adapterOps (Tx1Q_SameCut.dictionary ops reserved queryOps geoOps) B claimsStd)) () H (bytesOf f.proof.val) (bytesOf f.pub.val)
          (bytesOf saved.val) parsed ∧
        (∀ site, (observation f s saved nodes y1 pre middle fs ss (before e1 e2) (after e1 e2 post1)).reached site ↔
          S2W_SiteSchedule.Event.site site ∈ projected port outer) := by
  obtain ⟨f,s,validated,outer,pre,middle,fs,ss,cuts,getter,validation,encoder,expanded,owned,
    layout,unchanged,before1,before2,claims,caller⟩ :=
    Hist_SdkStrong.accepted_pair_claims L sdk copy std allocator e1 e2 w1 w2 admission1 admission2
      adapterOps (Tx1Q_SameCut.dictionary ops reserved queryOps geoOps) B claimsStd
      native1 native2 hashv extraction sha256 H p1 syscall program data1 data2 slot
      state1 state2 final1 final2 saved post1 post2 accepted1 accepted2 p root length port firstMarks secondMarks
  have header := Op3I_Cuts.same_cut_header adapterOps
    (Op4P_Install.install (Tx1Q_Execution.base ops reserved queryOps geoOps)) B claimsStd
    e1.first (e2.second secondSizes) saved f s cuts
  have scan := Op4P_Cuts.same_cut_scan adapterOps (Tx1Q_Execution.base ops reserved queryOps geoOps)
    B claimsStd e1.first (e2.second secondSizes) saved f s cuts
  exact ⟨f,s,validated,outer,pre,middle,fs,ss,cuts,getter,validation,encoder,header,scan,
    WAdm_NativeEndpoint.reached adapterOps ops reserved queryOps geoOps B claimsStd e1 _ saved f s cuts prepareOwner primitiveOwner,
    expanded,owned,layout,unchanged,before1,before2,claims,caller⟩

#print axioms accepted_pair_claims_tx1
#print accepted_pair_claims_tx1
end AspisR1.Hist_AcceptedStrong
end
