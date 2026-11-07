import NLS_COMBINED_IMPORT
import NLW_COMBINED_IMPORT
import NLT_CompleteRoot
import NMF_WriterRoots
import NMF_InputTransport
import NMF_ReachedHeader
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace NMF_GameRoot
open AspisR1
open IDa_Deployed
open OraclePortRuntimeBindingC7 Port1_StoredCarrier
open FS FS2
open AspisV8R19.OracleResampling
open F3T_Experiment F3T_Charged F3T_TwoPass F3T_ByteCarrier F3T_CanonicalJoin
open RawExtractorCostComposedV2
open OraclePortHeadlineFrozen2PerAttempt (Claims failureModel)
open scoped BigOperators
attribute [local instance] Classical.propDecidable
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
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem root0_or_existing_collision {W A CoreError Tx : Type}
    (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A)
    (e1 e2 : Entry) (w1 w2 : W)
    (admission1 : RuntimeEntrypointAdmission L e1 w1 3)
    (admission2 : RuntimeEntrypointAdmission L e2 w2 7)
    (missing : Uninstalled CoreError) (indexError : CoreError)
    (reservation : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk (FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation)) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (data1 data2 : Slice U8)
    (slot : S2W_ExtractionBoundary.Slot) (state1 state2 final1 final2 : A)
    (saved : alloc.vec.Vec U8) (post1 post2 : Heap (Nat → Record))
    (accepted1 : S2W_D189Wrappers.first native1 copy allocator e1 CPH_Program.verifier data1 state1 =
      ok (.Ok (saved,post1,final1)))
    (accepted2 : S2W_D189Wrappers.second native2 allocator e2 CPH_Program.verifier data2 slot state2 =
      ok (.Ok (post2,final2)))
    (root : Array U8 32#usize) (length : U32)

    (prior : Program Bytes State Unit)
    (words : CanonicalCutEnrichedTranscript.Words)
    (p : CPG_Projection.Observations Tx A) (t u : Tx)
    (actions : List (CPP_BankState.Action A))
    (game : CPH_Game.DeployedPairExecution p t u e1 e2 saved actions native1 native2 copy allocator CPH_Program.verifier)
    (RuntimePersistence : CPR_DataPersistence.TwoTransactionLaw
      (CPG_Projection.adjacent p) (CPG_Projection.ordinary p (Hist_Nonvacuity.key 0#u8)) (CPG_Projection.before p)
      (CPG_Projection.tentative p)
      (CPG_Projection.success p) (CPG_Projection.loaded p))
    (D : LiteralByteProtocol.Decoder) (a : SCE_Experiment.Adversary A) (Q0 Q1 : Nat)
    (queries : ∀ H : Bytes → State,
      (ARW_Induced.issued native1 copy allocator CPH_Program.verifier a H).length ≤ Q0+Q1)
    :
    let c := FJt_GlobalTerminal.configuration missing indexError reservation;
    let P := ARW_Induced.program native1 copy allocator CPH_Program.verifier a;
    let select : F3X_Projection.Output → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs :=
      fun _ => P2P_NativeSelection.pair (DrvC_Installation.sdk c)
        CPH_Program.verifier e1 e2 data2 slot;
    ∃ f s, SourceCuts (DrvC_Installation.sdk c) e1.first (e2.second secondSizes) saved f s ∧
      NLP_InputDomain.Root0 saved.deref f.proof ∧
      bytesOf s.checkpoint.val=bytesOf saved.val ∧
      (NLP_InputDomain.Root0 s.checkpoint s.proof ∨
        BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965)
          (eval H (Hiq_RecordedJoint.program (F3X_Account.program c hashv P)
            F3X_Projection.project select))) := by
  let c:=FJt_GlobalTerminal.configuration missing indexError reservation
  obtain ⟨p6,driver,sdkEq,original,security,copyFacts,events,protection,trace,recorder,installation⟩ :=
    AspisR1.RPx_Deployed.deployed L sdk copy std allocator e1 e2 w1 w2 admission1 admission2
      missing indexError reservation native1 native2 hashv extraction sha256 H p1 syscall data1 data2 slot
      state1 state2 final1 final2 saved post1 post2 accepted1 accepted2 root length prior words
      p t u actions game RuntimePersistence D a Q0 Q1 queries
  obtain ⟨f,s,outer,pre,middle,fs,ss,run,tx2,origin,calls,encoding,base,initial,selected,publicFacts,parser,
    version,writerKey,readerKey,physical,persistent,packet,safe,whole,caller⟩ := original
  have cuts:=base.1
  have oldRoot:=NMF_WriterRoots.physical _ _ _ _ _ _ _ _ _ _ _ _ _ run
  have savedRoot:=NMF_WriterRoots.serialized _ () _ _ f.proof f.pub saved run.writer_call oldRoot
  have persisted : bytesOf s.checkpoint.val=bytesOf saved.val := persistent.trans copyFacts.2.2.1
  refine ⟨f,s,cuts,savedRoot,persisted,?_⟩
  let P:=ARW_Induced.program native1 copy allocator CPH_Program.verifier a
  have queryBound : ∀ H, (eval H P).1.length≤Q0+Q1 := by
    intro H
    rw [ARW_Induced.queries]
    exact queries H
  have budget:=F3Y_AccountMass.budget
    (Rc2_Install.configuration (Rc5_Install.seed indexError
      (FIp_Install.select reservation (IDa_Deployed.deployedConfiguration missing indexError reservation))) reservation)
    hashv D words P (Q0+Q1) queryBound
  have alternative:=P2P_Charge.binding_or_collision
    (F3X_Account.program c hashv P) F3X_Projection.project
    (fun _ => P2P_NativeSelection.pair (DrvC_Installation.sdk c)
      CPH_Program.verifier e1 e2 data2 slot) (Q0+Q1) budget H
  rcases alternative with bad | good
  · exact Or.inr bad
  · have association:=P2P_NativeSelection.on_cuts (DrvC_Installation.sdk c)
      CPH_Program.verifier e1 e2 data2 slot saved f s cuts origin
    change R9PoolRuntimeBinding.P2Prime H
      (P2P_NativeSelection.pair (DrvC_Installation.sdk c) CPH_Program.verifier e1 e2 data2 slot).1
      (P2P_NativeSelection.pair (DrvC_Installation.sdk c) CPH_Program.verifier e1 e2 data2 slot).2 at good
    rw [association] at good
    obtain ⟨pm,written⟩:=encoding
    have writer:=NLW_WriterHeader.decoded H (bytesOf f.proof.val) (bytesOf f.pub.val) pm _
    have writerHeader : NLW_ReaderHeader.decode (bytesOf saved.val)=
      some (H (bytesOf f.proof.val),H (bytesOf f.pub.val)) := by
      rw [written,Tx2N_Reader.writer_bytes]
      exact writer
    have oracle : CheckpointBytes5Inputs.Oracle
      (VTop_Checkpoint.digest (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (DrvC_Installation.sdk c))) () H := by
      intro parts digest returned
      change (DrvC_Installation.sdk c).op43 () parts=ok digest at returned
      rw [extraction.digestSource,S2W_DigestExtraction.digest_eq_hashv] at returned
      exact (syscall.returningValue parts digest returned).trans (p1.realization _)
    have readerHeader:=NMF_ReachedHeader.returned _ _ _ _ _ _ () H oracle s.pub s.proof s.checkpoint tx2 calls
    have matched:=NLW_AuthenticatedRoots.digest_matches H saved.deref s.checkpoint
      f.proof f.pub s.proof s.pub persisted writerHeader readerHeader
    have equal:=good matched
    exact Or.inl (NMF_InputTransport.root0 saved.deref s.checkpoint f.proof s.proof savedRoot persisted equal.1)
#print root0_or_existing_collision
#print axioms root0_or_existing_collision
end NMF_GameRoot
end
