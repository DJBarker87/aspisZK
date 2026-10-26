import CPP_Close
import CPP_Origin
import T2R_Top
import T2Nat_NativePair
import AuS1_Accepted
import DrvC_SourceHeadline
import Cons_Pair
import Cons_Finish
import Cons_Native
import Cons_Continuation
import Cons_Base
import Cons_Caller
import Cons_Result
import T2R_FullResult
import T2R_Pair
import Par_Headline
import Par_Transcript
import Cons_NativeBuild
import Cons_FinishProof
import Cons_Second
import T2Nat_ReaderEffects
import CPhy_Physical
import T2Nat_FinishResult
import CPhy_Header
import CPhy_Ranges
import CPhy_Accepted
import WAdm_NativeEndpoint
import SdkD_Accepted
import SdkD_Inner
import SdkD_Uni
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.CPP_RuntimeTop
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

theorem deployed {W A F CoreError : Type}
    (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A)
    (c : DrvC_Installation.Configuration F CoreError)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (prepareOwner : WAdm_Domain.SessionAPrepare
      (Tx1Q_Execution.actual (Op5T_Concrete.current (DrvC_FirstConstants.configuration c).currentBase)
        (DrvC_FirstConstants.configuration c).reserved (DrvC_FirstConstants.configuration c).query (DrvC_FirstConstants.configuration c).geometry (DrvC_FirstConstants.configuration c).boundaries (DrvC_FirstConstants.configuration c).std))
    (primitiveOwner : Port5Q1_QueryPorts.SessionAPrimitives (DrvC_FirstConstants.configuration c).query)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk (DrvC_FirstConstants.configuration c)) native1 native2 hashv)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (program : S2W_ExtractionBoundary.Program)
    (root : Array U8 32#usize) (length : U32) (prior : Program Bytes State Unit)
    (D : LiteralByteProtocol.Decoder) (P : ByteProver) (Q0 Q1 : Nat)
    (hqueries : ∀ H : Bytes → State, (eval H P).1.length ≤ Q0+Q1)
    (runtime : Runtime)
    (raw : Port1_CanonicalJoin.AcceptedVerifierJoin D (DrvC_SourceEntry.source (DrvC_FirstConstants.configuration c) hashv))
    (binding : StoredCarrierBinding D (DrvC_SourceEntry.source (DrvC_FirstConstants.configuration c) hashv) (lift P) runtime)
    (adversary : Program Bytes State GExp_Experiment.FirstInputs)
    (chooseSecond : GExp_Experiment.FirstInputs → alloc.vec.Vec U8 → Program Bytes State GExp_Experiment.SecondInputs)
    (prefixBound : ∀ H, (eval H adversary).1.length ≤ Q0)
    (choiceBound : ∀ input saved H, (eval H (chooseSecond input saved)).1.length ≤ Q1)
    (project : GExp_Experiment.Outcome → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (initial : Hist_Store.Store) (schedule : CPP_Schedule.Schedule A (Hir_Call.Call A)) (count2 : Nat)
    (law : (DrvC_Installation.sdk (DrvC_FirstConstants.configuration c)).op36 = Hist_Authority.keyEq)
    (genesis : ∀ key, (initial key).owner = program → ¬ Hist_Store.Initialized (initial key).data)
    (allowed : Hir_ProvenanceModel.admissible native1 native2 copy allocator program H initial (CPP_Schedule.erase schedule))
    (post2 : Heap (Nat → Record)) (final2 : A)
    (accepted2 : let out := CPP_Schedule.run native1 native2 copy allocator program H initial schedule
      CPP_Invocation.second native2 allocator program out.1 ⟨out.2.2,count2⟩ = ok (.Ok (post2,final2)))
    (world : Hir_ProvenanceModel.CallAt A → W) (w2 : W)
    (admission1 : ∀ site ∈ Hir_ProvenanceModel.calls native1 native2 copy allocator program H initial (CPP_Schedule.erase schedule),
      RuntimeEntrypointAdmission L (Hist_RuntimeEntry.load site.before site.call.layout) (world site) 3)
    (admission2 : let out := CPP_Schedule.run native1 native2 copy allocator program H initial schedule
      RuntimeEntrypointAdmission L (Hist_RuntimeEntry.load out.1 out.2.2.layout) w2 7) :
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
    (let out := CPP_Schedule.run native1 native2 copy allocator program H initial schedule
    ∃ writer : Hir_WriterSelect.Writer A,
      Hir_WriterSelect.search native1 copy allocator program (out.2.2.layout.handles 6).1 (out.1 (out.2.2.layout.handles 6).1).data (Hir_ProvenanceModel.calls native1 native2 copy allocator program H initial (CPP_Schedule.erase schedule)) = some writer ∧
      CPP_FullResult.Outcome L (Hist_RuntimeEntry.load writer.site.before writer.site.call.layout) (Hist_RuntimeEntry.load out.1 out.2.2.layout) (world writer.site) w2
        (DrvC_FirstConstants.configuration c).adapter (DrvC_FirstConstants.configuration c).currentBase (DrvC_FirstConstants.configuration c).reserved (DrvC_FirstConstants.configuration c).query (DrvC_FirstConstants.configuration c).geometry (DrvC_FirstConstants.configuration c).stageBase (DrvC_FirstConstants.configuration c).finish (DrvC_FirstConstants.configuration c).boundaries (DrvC_FirstConstants.configuration c).std program writer.site.call.data out.2.2.data out.2.2.slot
        writer.saved writer.post post2 H (DrvC_Implementation.driver (DrvC_FirstConstants.configuration c)) prior) := by
  let out := CPP_Schedule.run native1 native2 copy allocator program H initial schedule
  obtain ⟨count,writer,found,member,birth,accepted1,second⟩ := CPP_Origin.selected
    (DrvC_FirstConstants.configuration c) law native1 native2 hashv extraction copy allocator program sha256 H p1 syscall
    initial schedule count2 genesis allowed post2 final2 accepted2
  obtain ⟨implementation,dictionary,headline,pair⟩ := T2R_Top.deployed L sdk copy std allocator
    (Hist_RuntimeEntry.load writer.site.before writer.site.call.layout) (Hist_RuntimeEntry.load out.1 out.2.2.layout) (world writer.site) w2 (admission1 writer.site member) admission2
    c native1 native2 prepareOwner primitiveOwner hashv extraction sha256 H p1 syscall program
    writer.site.call.data out.2.2.data out.2.2.slot writer.site.call.state out.2.2.state writer.final final2
    writer.saved writer.post post2 accepted1 second root length prior D P Q0 Q1 hqueries runtime raw binding
    adversary chooseSecond prefixBound choiceBound project
  refine ⟨implementation,dictionary,headline,writer,found,?_⟩
  exact CPP_Close.closed L (world writer.site) w2 (DrvC_FirstConstants.configuration c) law native1 native2 hashv extraction
    copy std allocator program H initial schedule writer found post2 (DrvC_Implementation.driver (DrvC_FirstConstants.configuration c)) prior pair

#print axioms deployed
end AspisR1.CPP_RuntimeTop
end
