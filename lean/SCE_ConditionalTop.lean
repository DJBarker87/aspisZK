import Rc5_Top
import SCE_SubmissionBound
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.SCE_ConditionalTop
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


/-- Quantifier-corrected shared-account endpoint. This stage explicitly
RETAINS L159/binding; no discharge is claimed. Both native submissions and
the game entries are response-selected from the SAME adversary in H. -/
theorem deployed {W A F CoreError Tx : Type}
    (L : Library W (Nat → Record))
    (sdk : S2TrustedSdkBorrow L)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy)
    (allocator : Allocator A)
    (c : DrvC_Installation.Configuration F CoreError)
    (indexError : CoreError)
    (reservation : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First)
    (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk (Rc5_Install.configuration indexError c reservation)) native1 native2 hashv)
    (experiment : SCE_Experiment.Adversary A)
    (sha256 H : Bytes → State)
    (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (saved : alloc.vec.Vec U8)
    (post1 post2 : Heap (Nat → Record))
    (final1 final2 : A)
    (w1 w2 : W)
    (admission1 : RuntimeEntrypointAdmission L ((eval H experiment.first).2.entry) w1 3)
    (admission2 : RuntimeEntrypointAdmission L ((eval H (experiment.second (eval H experiment.first).2 saved post1 final1)).2.entry) w2 7)
    (accepted1 : S2W_D189Wrappers.first native1 copy allocator ((eval H experiment.first).2.entry) CPH_Program.verifier ((eval H experiment.first).2.data) ((eval H experiment.first).2.state) =
      ok (.Ok (saved,post1,final1)))
    (accepted2 : S2W_D189Wrappers.second native2 allocator ((eval H (experiment.second (eval H experiment.first).2 saved post1 final1)).2.entry) CPH_Program.verifier ((eval H (experiment.second (eval H experiment.first).2 saved post1 final1)).2.data) ((eval H (experiment.second (eval H experiment.first).2 saved post1 final1)).2.slot) ((eval H (experiment.second (eval H experiment.first).2 saved post1 final1)).2.state) =
      ok (.Ok (post2,final2)))
    (root : Array U8 32#usize)
    (length : U32)
    (prior : Program Bytes State Unit)
    (words : CanonicalCutEnrichedTranscript.Words)
    (p : CPG_Projection.Observations Tx A)
    (t u : Tx)
    (actions : List (CPP_BankState.Action A))
    (game : CPH_Game.DeployedPairExecution p t u ((eval H experiment.first).2.entry) ((eval H (experiment.second (eval H experiment.first).2 saved post1 final1)).2.entry) saved actions native1 native2 copy allocator CPH_Program.verifier)
    (RuntimePersistence : CPR_DataPersistence.TwoTransactionLaw
      (CPG_Projection.adjacent p) (CPG_Projection.ordinary p (Hist_Nonvacuity.key 0#u8)) (CPG_Projection.before p)
      (CPG_Projection.tentative p)
      (CPG_Projection.success p) (CPG_Projection.loaded p))
    (D : LiteralByteProtocol.Decoder)
    (Q0 Q1 : Nat)
    (raw : F3T_CanonicalJoin.AcceptedVerifierJoin
      (Rc5_Install.configuration indexError c reservation) D
      (F3T_Installed.source (Rc5_Install.configuration indexError c reservation) hashv))
    (binding : F3T_Runtime.StoredCarrierBinding
      (Rc5_Install.configuration indexError c reservation) D
      (F3T_Installed.source (Rc5_Install.configuration indexError c reservation) hashv) (SCE_Experiment.submission experiment) (SCE_Experiment.runtime (Rc5_Install.configuration indexError c reservation) hashv copy allocator CPH_Program.verifier experiment))
    (prefixBound : ∀ H, (eval H experiment.first).1.length ≤ Q0)
    (choiceBound : ∀ input saved post final H, (eval H (experiment.second input saved post final)).1.length ≤ Q1)
    (project : GExq_AccountExperiment.Outcome A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (select : GExq_AccountExperiment.Outcome A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs) :

    DrvC_Implementation.driver (Rc5_Install.configuration indexError c reservation) = DrvC_SourceEntry.source (Rc5_Install.configuration indexError c reservation) hashv ∧
    DrvC_Installation.sdk (Rc5_Install.configuration indexError c reservation) =
      SdkD_PairBatches.dictionary (Rc5_Install.configuration indexError c reservation).adapter (Rc5_Install.configuration indexError c reservation).currentBase (Rc5_Install.configuration indexError c reservation).stageBase
        (Rc5_Install.configuration indexError c reservation).finish (Rc5_Install.configuration indexError c reservation).reserved (Rc5_Install.configuration indexError c reservation).query (Rc5_Install.configuration indexError c reservation).geometry
        (Rc5_Install.configuration indexError c reservation).boundaries (Rc5_Install.configuration indexError c reservation).std ∧
    (Rc5_Result.Outcome L ((eval H experiment.first).2.entry) ((eval H (experiment.second (eval H experiment.first).2 saved post1 final1)).2.entry) w1 w2
      (Rc5_Install.configuration indexError c reservation).adapter (Rc5_Install.configuration indexError c reservation).currentBase
      (Rc5_Install.configuration indexError c reservation).reserved (Rc5_Install.configuration indexError c reservation).query
      (Rc5_Install.configuration indexError c reservation).geometry (Rc5_Install.configuration indexError c reservation).stageBase
      (Rc5_Install.configuration indexError c reservation).finish c.boundaries
      reservation CPH_Program.verifier ((eval H experiment.first).2.data) ((eval H (experiment.second (eval H experiment.first).2 saved post1 final1)).2.data) ((eval H (experiment.second (eval H experiment.first).2 saved post1 final1)).2.slot) saved post1 post2 H
      (DrvC_Implementation.driver (Rc5_Install.configuration indexError c reservation)) prior
      (p.physicalEvents t)) ∧
    ((∀ H : Bytes → State,(eval H (annotatedWith D (F3T_Installed.source (Rc5_Install.configuration indexError c reservation) hashv)
        (F3T_Canon.canon (lift (Rc5_Install.configuration indexError c reservation) (SCE_Experiment.submission experiment))))).2.2=true →
      mean (fun coins : Coins=>((ActualCostedExtractorM10.extractor.eval
        (view (eval H (annotatedWith D (F3T_Installed.source (Rc5_Install.configuration indexError c reservation) hashv) (F3T_Canon.canon (lift (Rc5_Install.configuration indexError c reservation) (SCE_Experiment.submission experiment)))))) coins).2.total : Rat))≤
          ((CostedAllocationLedgerM10.params (Q0+Q1+1161)).attemptBudget : Rat)) ∧
    (∀ run coins w,(ActualCostedExtractorM10.extractor.eval run coins).1=some w →
      LiteralProtocol.relation run.2.1.1 w) ∧
    (1/(2:Rat)^126+1/(2:Rat)^454≤1/(2:Rat)^120) ∧
    (F3T_RuntimeBound.failureModel (SCE_Experiment.runtime (Rc5_Install.configuration indexError c reservation) hashv copy allocator CPH_Program.verifier experiment)≤StartChargeNumeric.totalBound (Q0+Q1)) ∧
    (Q0+Q1≤OraclePortHeadlineFrozen2.Qmax → F3T_RuntimeBound.failureModel (SCE_Experiment.runtime (Rc5_Install.configuration indexError c reservation) hashv copy allocator CPH_Program.verifier experiment)≤(Q0+Q1+1:Rat)*(1/(2:Rat)^100))) ∧
    (let r := Rc5_Install.configuration indexError c reservation;
      F3T_RuntimeBound.failureModel (SCE_Experiment.runtime (Rc5_Install.configuration indexError c reservation) hashv copy allocator CPH_Program.verifier experiment) +
        F3T_AccountCharge.mass (CPG_Account.source r hashv copy allocator CPH_Program.verifier experiment.first experiment.second)
          project select (Q0+Q1) ≤ F3T_Numeric.total (Q0+Q1)) ∧
    (let r := Rc5_Install.configuration indexError c reservation;
      Q0+Q1 = 0 → F3T_RuntimeBound.failureModel (SCE_Experiment.runtime (Rc5_Install.configuration indexError c reservation) hashv copy allocator CPH_Program.verifier experiment) +
        F3T_AccountCharge.mass (CPG_Account.source r hashv copy allocator CPH_Program.verifier experiment.first experiment.second)
          project select (Q0+Q1) < 1/(2:Rat)^100) ∧
    (native1 CPH_Program.verifier ((eval H experiment.first).2.entry).first ((eval H experiment.first).2.data) = ok (.Ok saved) ∧
      saved.val.length = 1768 ∧
      payloadBytes encode (post1.payload (((eval H experiment.first).2.entry).heap.accounts 2).1) 1768 = bytesOf saved.val ∧
      post1.ambient = ((eval H experiment.first).2.entry).heap.ambient ∧ post1.accounts = ((eval H experiment.first).2.entry).heap.accounts ∧
      post1.counter = ((eval H experiment.first).2.entry).heap.counter ∧
      (∀ cell, cell ≠ (((eval H experiment.first).2.entry).heap.accounts 2).1 → post1.payload cell = ((eval H experiment.first).2.entry).heap.payload cell)) ∧
    Rc2_Events.Facts (Rc5_Install.configuration indexError c reservation) hashv native1 native2 copy allocator CPH_Program.verifier H saved ∧
    CPH_Protection.Facts p t saved CPH_Program.verifier ∧
    CPH_Trace.Facts p t u saved native1 native2 copy allocator CPH_Program.verifier ∧
    CPH_Recorder.Facts (Rc5_Install.configuration indexError c reservation) hashv native1 native2 copy allocator
      CPH_Program.verifier H p t u saved := by
  exact Rc5_Top.deployed L sdk copy std allocator ((eval H experiment.first).2.entry) ((eval H (experiment.second (eval H experiment.first).2 saved post1 final1)).2.entry) w1 w2 admission1 admission2
      c indexError reservation native1 native2 hashv extraction sha256 H p1 syscall
      ((eval H experiment.first).2.data) ((eval H (experiment.second (eval H experiment.first).2 saved post1 final1)).2.data) ((eval H (experiment.second (eval H experiment.first).2 saved post1 final1)).2.slot) ((eval H experiment.first).2.state) ((eval H (experiment.second (eval H experiment.first).2 saved post1 final1)).2.state) final1 final2 saved post1 post2 accepted1 accepted2 root length
      prior words p t u actions game RuntimePersistence D (SCE_Experiment.submission experiment) Q0 Q1
      (SCE_SubmissionBound.queries experiment Q0 Q1 prefixBound) (SCE_Experiment.runtime (Rc5_Install.configuration indexError c reservation) hashv copy allocator CPH_Program.verifier experiment) raw binding
      experiment.first experiment.second prefixBound choiceBound project select

#print axioms deployed
#print deployed
end AspisR1.SCE_ConditionalTop
end
