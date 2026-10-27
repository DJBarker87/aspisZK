import RPz7_CPS_BankRecorder
import RPz7_CPR_DataWriter
import RPz7_CPR_PhysicalResult
import RPz7_T2R_Top
import RPz7_T2Nat_NativePair
import RPz7_AuS1_Accepted
import RPz7_DrvC_SourceHeadline
import RPz7_Cons_Pair
import RPz7_Cons_Finish
import RPz7_Cons_Native
import RPz7_Cons_Continuation
import RPz7_Cons_Base
import RPz7_Cons_Caller
import RPz7_Cons_Result
import RPz7_T2R_FullResult
import RPz7_T2R_Pair
import RPz7_Par_Headline
import RPz7_Par_Transcript
import RPz7_Cons_NativeBuild
import RPz7_Cons_FinishProof
import RPz7_Cons_Second
import RPz7_T2Nat_ReaderEffects
import RPz7_CPhy_Physical
import T2Nat_FinishResult
import RPz7_CPhy_Header
import RPz7_CPhy_Ranges
import RPz7_CPhy_Accepted
import RPz7_WAdm_NativeEndpoint
import RPz7_SdkD_Accepted
import RPz7_SdkD_Inner
import RPz7_SdkD_Uni
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.CPS_SourceTop
open OraclePortRuntimeBindingC7 Port1_StoredCarrier
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

/-- Same original root and witnesses, with ordered events computed by the
source-bank recorder. The physical/source association, pairing, parent status,
loader and ordinary-key interpretations remain explicit and uninstantiated.
This is not the requested single-law deployed closure. -/
theorem correlated {W A F CoreError Tx Key : Type}
    (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A)
    (e1 e2 : Entry) (w1 w2 : W)
    (admission1 : RuntimeEntrypointAdmission L e1 w1 3)
    (admission2 : RuntimeEntrypointAdmission L e2 w2 7)
    (c : DrvC_Installation.Configuration F CoreError)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (prepareOwner : WAdm_Domain.SessionAPrepare
      (Tx1Q_Execution.actual (Op5T_Concrete.current (DrvC_FirstConstants.configuration c).currentBase) (DrvC_FirstConstants.configuration c).reserved (DrvC_FirstConstants.configuration c).query (DrvC_FirstConstants.configuration c).geometry (DrvC_FirstConstants.configuration c).boundaries (DrvC_FirstConstants.configuration c).std))
    (primitiveOwner : Port5Q1_QueryPorts.SessionAPrimitives (DrvC_FirstConstants.configuration c).query)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (sdkOps (Tx2I_Install.install (DrvC_FirstConstants.configuration c).adapter (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base (DrvC_FirstConstants.configuration c).stageBase) (DrvC_FirstConstants.configuration c).reserved (DrvC_FirstConstants.configuration c).query (DrvC_FirstConstants.configuration c).geometry)) (DrvC_FirstConstants.configuration c).finish) (Uni_Install.current (DrvC_FirstConstants.configuration c).currentBase (DrvC_FirstConstants.configuration c).reserved (DrvC_FirstConstants.configuration c).query (DrvC_FirstConstants.configuration c).geometry) (DrvC_FirstConstants.configuration c).boundaries (DrvC_FirstConstants.configuration c).std) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (program : S2W_ExtractionBoundary.Program) (data1 data2 : Slice U8)
    (slot : S2W_ExtractionBoundary.Slot) (state1 state2 final1 final2 : A)
    (saved : alloc.vec.Vec U8) (post1 post2 : Heap (Nat → Record))
    (accepted1 : S2W_D189Wrappers.first native1 copy allocator e1 program data1 state1 =
      ok (.Ok (saved,post1,final1)))
    (accepted2 : S2W_D189Wrappers.second native2 allocator e2 program data2 slot state2 =
      ok (.Ok (post2,final2)))
    (root : Array U8 32#usize) (length : U32)

    (prior : Program Bytes State Unit)
    (D : LiteralByteProtocol.Decoder) (P : ByteProver) (Q0 Q1 : Nat)
    (hqueries : ∀ H : Bytes → State, (eval H P).1.length ≤ Q0+Q1)
    (runtime : Runtime)
    (raw : Port1_CanonicalJoin.AcceptedVerifierJoin D (DrvC_SourceEntry.source (DrvC_FirstConstants.configuration c) hashv))
    (binding : StoredCarrierBinding D (DrvC_SourceEntry.source (DrvC_FirstConstants.configuration c) hashv) (lift P) runtime)
    (adversary : Program Bytes State GExp_Experiment.FirstInputs)
    (chooseSecond : GExp_Experiment.FirstInputs → alloc.vec.Vec U8 →
      Program Bytes State GExp_Experiment.SecondInputs)
    (prefixBound : ∀ H, (eval H adversary).1.length ≤ Q0)
    (choiceBound : ∀ input saved H, (eval H (chooseSecond input saved)).1.length ≤ Q1)
    (project : GExp_Experiment.Outcome → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (keyLaw : (DrvC_Installation.sdk (DrvC_FirstConstants.configuration c)).op36 = Hist_Authority.keyEq)
    (initial : CPP_BankState.Bank) (layout1 : Hist_RuntimeEntry.Layout)
    (entry1 : e1 = Hist_RuntimeEntry.load initial.cells (CPP_BankState.layout initial layout1))
    (actions : List (CPP_BankState.Action A))
    (positive : 0 < initial.lamports (layout1.handles 2).1)
    (next : Tx → Tx → Prop) (ordinary : Tx → Key → Prop)
    (before tentative : Tx → Key → CPR_DataPersistence.Image) (success : Tx → Bool)
    (loaded : Tx → Key → Option Bytes)
    (law : CPR_DataPersistence.TwoTransactionLaw next ordinary before tentative success loaded)
    (t u : Tx) (physicalKey : Key) (adjacent : next t u) (eligible : ordinary t physicalKey)
    (tentativeView : tentative t physicalKey = CPR_DataPersistence.snapshot
      (CPP_BankHistory.run native1 native2 copy allocator program
        (CPR_SourceBank.afterCopy initial (layout1.handles 2).1 saved) actions).1 (layout1.handles 2).1)
    (status : success t = true)
    (entry2View : loaded u physicalKey = some (bytesOf (e2.buffers (e2.handles 6).1).val)) :
    DrvC_Implementation.driver (DrvC_FirstConstants.configuration c) =
      DrvC_SourceEntry.source (DrvC_FirstConstants.configuration c) hashv ∧
    DrvC_Installation.sdk (DrvC_FirstConstants.configuration c) =
      SdkD_PairBatches.dictionary (DrvC_FirstConstants.configuration c).adapter
        (DrvC_FirstConstants.configuration c).currentBase (DrvC_FirstConstants.configuration c).stageBase
        (DrvC_FirstConstants.configuration c).finish (DrvC_FirstConstants.configuration c).reserved
        (DrvC_FirstConstants.configuration c).query (DrvC_FirstConstants.configuration c).geometry
        (DrvC_FirstConstants.configuration c).boundaries (DrvC_FirstConstants.configuration c).std ∧
    (let r := DrvC_FirstConstants.configuration c
    let source := GExp_Experiment.program
      (GExp_FirstPair.base r.currentBase r.reserved r.query r.geometry)
      (DrvC_Installation.stage r) r.reserved r.boundaries r.std hashv
      (DrvC_Installation.currentDigest r) (DrvC_Installation.digest r) adversary chooseSecond
    Claims D (lift P) (Q0+Q1) runtime ∧
    (failureModel runtime + EndP_AuthMass.mass source project ≤
      ((Q0+Q1+34 : Nat) : Rat)*PerAttemptEnvelope.B +
      (6*((Q0+Q1+1161 : Nat) : Rat)^2/(2:Rat)^256 +
       6*((Q0+Q1+23625 : Nat) : Rat)^2/(2:Rat)^256) +
      1/(2:Rat)^126 + 1/(2:Rat)^454) ∧
    (Q0+Q1 = 0 → failureModel runtime + EndP_AuthMass.mass source project ≤ 1/(2:Rat)^100)) ∧
    (CPR_PhysicalResult.Outcome L e1 e2 w1 w2 (DrvC_FirstConstants.configuration c).adapter (DrvC_FirstConstants.configuration c).currentBase (DrvC_FirstConstants.configuration c).reserved (DrvC_FirstConstants.configuration c).query (DrvC_FirstConstants.configuration c).geometry (DrvC_FirstConstants.configuration c).stageBase (DrvC_FirstConstants.configuration c).finish (DrvC_FirstConstants.configuration c).boundaries (DrvC_FirstConstants.configuration c).std program data1 data2 slot saved post1 post2 H (DrvC_Implementation.driver (DrvC_FirstConstants.configuration c)) prior (eval H (CPS_BankRecorder.program (DrvC_FirstConstants.configuration c) hashv native1 native2 copy allocator program (CPR_SourceBank.afterCopy initial (layout1.handles 2).1 saved) actions)).2.2) := by
  obtain ⟨driverEq,sdkEq,headline,original⟩ := T2R_Top.deployed
    L sdk copy std allocator e1 e2 w1 w2 admission1 admission2 c native1 native2
    prepareOwner primitiveOwner hashv extraction sha256 H p1 syscall program data1 data2 slot
    state1 state2 final1 final2 saved post1 post2 accepted1 accepted2 root length prior
    D P Q0 Q1 hqueries runtime raw binding adversary chooseSecond prefixBound choiceBound project
  obtain ⟨f,s,outer,pre,middle,fs,ss,run,tx2,calls,base,publicFacts,parser,acceptance,caller⟩ := original
  let version := CPR_DataWriter.on_cuts (DrvC_FirstConstants.configuration c) keyLaw native1 native2 hashv extraction
    copy std allocator program initial (CPP_BankState.layout initial layout1) e1 e2 entry1 data1 state1 final1 saved post1 accepted1 actions positive
    next ordinary before tentative success loaded law t u physicalKey adjacent eligible tentativeView status entry2View f s base.1
  have eventMatch : version.events = (eval H (CPS_BankRecorder.program (DrvC_FirstConstants.configuration c) hashv native1 native2 copy allocator program (CPR_SourceBank.afterCopy initial (layout1.handles 2).1 saved) actions)).2.2 := by
    change (CPP_BankHistory.run native1 native2 copy allocator program
      (CPR_SourceBank.afterCopy initial (layout1.handles 2).1 saved) actions).2 = (eval H (CPS_BankRecorder.program (DrvC_FirstConstants.configuration c) hashv native1 native2 copy allocator program (CPR_SourceBank.afterCopy initial (layout1.handles 2).1 saved) actions)).2.2
    exact (CPS_BankRecorder.events (DrvC_FirstConstants.configuration c) hashv native1 native2 copy allocator program extraction sha256 H p1 syscall
      (CPR_SourceBank.afterCopy initial (layout1.handles 2).1 saved) actions).symm
  refine ⟨driverEq,sdkEq,headline,f,s,outer,pre,middle,fs,ss,run,tx2,calls,base,publicFacts,parser,
    version,eventMatch,S2X.checkpoint_persistence _ _ version,?_,?_⟩
  · obtain ⟨i,pub,proof,tag,size,fit,accepted⟩ := acceptance
    exact ⟨i,pub,proof,tag,size,fit,fun p2prime => accepted version p2prime⟩
  · exact caller version

#print axioms correlated
end AspisR1.CPS_SourceTop
end
