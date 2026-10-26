import ARW_Root
import ARW_Observations
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.ARW_Residual
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

/-- Exact remaining mathematical obligation for the literal unfiltered
candidate. Same antecedents; no new trust item or adopted security theorem. -/
def Numeric : Prop := ∀ {W A CoreError Tx : Type}
    (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A)
    (e1 e2 : Entry) (w1 w2 : W)
    (admission1 : RuntimeEntrypointAdmission L e1 w1 3)
    (admission2 : RuntimeEntrypointAdmission L e2 w2 7)
    (c : DrvC_Installation.Configuration FIo_Install.W CoreError) (indexError : CoreError)
    (reservation : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk (FIp_Install.configuration indexError c reservation)) native1 native2 hashv)
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
    (finishOwners : FIp_GlobalOwners.Owners
      (FIp_Install.configuration indexError c reservation)
      (Rc2_Install.configuration (Rc5_Install.seed indexError (FIp_Install.select reservation c)) reservation).boundaries)
    ,
    let P := ARW_Induced.program native1 copy allocator CPH_Program.verifier a;
    let runtime := ART_Runtime.runtime (FIp_Install.configuration indexError c reservation)
      hashv copy allocator CPH_Program.verifier a;
    let select : F3X_Projection.Output → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs :=
      fun _ => P2P_NativeSelection.pair
        (DrvC_Installation.sdk (FIp_Install.configuration indexError c reservation))
        CPH_Program.verifier e1 e2 data2 slot;
    F3T_RuntimeBound.failureModel runtime ≤ F3T_Numeric.total (Q0+Q1)

/-- Statement characterization, not premise removal. -/
theorem characterization : ARW_Root.Requested ↔ Numeric := by
  constructor
  · intro h W A CoreError Tx L sdk copy std allocator e1 e2 w1 w2 admission1 admission2 c indexError reservation
      native1 native2 hashv extraction sha256 H p1 syscall data1 data2 slot state1 state2 final1 final2
      saved post1 post2 accepted1 accepted2 root length prior words p t u actions game RuntimePersistence
      D a Q0 Q1 queries finishOwners
    have full := h L sdk copy std allocator e1 e2 w1 w2 admission1 admission2 c indexError reservation
      native1 native2 hashv extraction sha256 H p1 syscall data1 data2 slot state1 state2 final1 final2
      saved post1 post2 accepted1 accepted2 root length prior words p t u actions game RuntimePersistence
      D a Q0 Q1 queries finishOwners
    exact full.2.2.2.2.1.2.2.2.1
  · intro h W A CoreError Tx L sdk copy std allocator e1 e2 w1 w2 admission1 admission2 c indexError reservation
      native1 native2 hashv extraction sha256 H p1 syscall data1 data2 slot state1 state2 final1 final2
      saved post1 post2 accepted1 accepted2 root length prior words p t u actions game RuntimePersistence
      D a Q0 Q1 queries finishOwners
    have security := h L sdk copy std allocator e1 e2 w1 w2 admission1 admission2 c indexError reservation
      native1 native2 hashv extraction sha256 H p1 syscall data1 data2 slot state1 state2 final1 final2
      saved post1 post2 accepted1 accepted2 root length prior words p t u actions game RuntimePersistence
      D a Q0 Q1 queries finishOwners
    obtain ⟨p6,driver,sdkEq,result,claims,copyFacts,events,protection,trace,recorder,s6⟩ :=
      ARW_Observations.observations L sdk copy std allocator e1 e2 w1 w2 admission1 admission2 c indexError reservation
        native1 native2 hashv extraction sha256 H p1 syscall data1 data2 slot state1 state2 final1 final2
        saved post1 post2 accepted1 accepted2 root length prior words p t u actions game RuntimePersistence
        D a Q0 Q1 queries finishOwners
    refine ⟨p6,driver,sdkEq,result,?_,copyFacts,events,protection,trace,recorder,s6⟩
    refine ⟨claims.1,claims.2.1,claims.2.2,security,?_,?_⟩
    · intro range
      simpa only [Nat.cast_add] using security.trans (F3U_Range.per_attempt _ range)
    · intro zero
      rw [zero] at security
      exact F3U_Numeric.runtime_margin _ security

#print axioms characterization
end AspisR1.ARW_Residual
end
