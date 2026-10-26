import CPH_Game
import CPH_Install
import CPH_Result
import CPG_History
import CPR_PhysicalResult
import CPG_Result
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
namespace AspisR1.CPH_Pair
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

theorem accepted {W A F CoreError Tx : Type}
    (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A)
    (e1 e2 : Entry) (w1 w2 : W)
    (admission1 : RuntimeEntrypointAdmission L e1 w1 3)
    (admission2 : RuntimeEntrypointAdmission L e2 w2 7)
    (input : DrvC_Installation.Configuration F CoreError)
    (reservation : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (prepareOwner : WAdm_Domain.SessionAPrepare
      (Tx1Q_Execution.actual (Op5T_Concrete.current (CPH_Install.configuration input reservation).currentBase) (CPH_Install.configuration input reservation).reserved (CPH_Install.configuration input reservation).query (CPH_Install.configuration input reservation).geometry (CPH_Install.configuration input reservation).boundaries (CPH_Install.configuration input reservation).std))
    (primitiveOwner : Port5Q1_QueryPorts.SessionAPrimitives (CPH_Install.configuration input reservation).query)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (sdkOps (Tx2I_Install.install (CPH_Install.configuration input reservation).adapter (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base (CPH_Install.configuration input reservation).stageBase) (CPH_Install.configuration input reservation).reserved (CPH_Install.configuration input reservation).query (CPH_Install.configuration input reservation).geometry)) (CPH_Install.configuration input reservation).finish) (Uni_Install.current (CPH_Install.configuration input reservation).currentBase (CPH_Install.configuration input reservation).reserved (CPH_Install.configuration input reservation).query (CPH_Install.configuration input reservation).geometry) (CPH_Install.configuration input reservation).boundaries (CPH_Install.configuration input reservation).std) native1 native2 hashv)
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
    (p : CPG_Projection.Observations Tx A) (t u : Tx)
    (actions : List (CPP_BankState.Action A))
    (game : CPH_Game.DeployedPairExecution p t u e1 e2 saved actions native1 native2 copy allocator program)
    (system : S2W_ExtractionBoundary.Program) (programNotSystem : program ≠ system)
    (keyLaw : (DrvC_Installation.sdk (CPH_Install.configuration input reservation)).op36 = Hist_Authority.keyEq)
    (RuntimePersistence : CPR_DataPersistence.TwoTransactionLaw
      (CPG_Projection.adjacent p) (CPG_Projection.ordinary p system) (CPG_Projection.before p)
      (CPG_Projection.tentative p)
      (CPG_Projection.success p) (CPG_Projection.loaded p)) :
    CPH_Result.Outcome L e1 e2 w1 w2
      (CPH_Install.configuration input reservation).adapter (CPH_Install.configuration input reservation).currentBase
      (CPH_Install.configuration input reservation).reserved (CPH_Install.configuration input reservation).query
      (CPH_Install.configuration input reservation).geometry (CPH_Install.configuration input reservation).stageBase
      (CPH_Install.configuration input reservation).finish (CPH_Install.configuration input reservation).boundaries
      reservation program data1 data2 slot saved post1 post2 H
      (DrvC_Implementation.driver (CPH_Install.configuration input reservation)) prior (CPH_Install.configuration input reservation) hashv native1 native2 copy allocator
      (p.physicalEvents t) := by
  let c := CPH_Install.select input reservation
  have oldGame := CPH_Game.recordedInstance game
  obtain ⟨f,s,outer,pre,middle,fs,ss,run,tx2,calls,base,publicFacts,caller⟩ :=
    T2R_Pair.accepted L sdk copy std allocator e1 e2 w1 w2 admission1 admission2
    (CPH_Install.configuration input reservation).adapter (CPH_Install.configuration input reservation).currentBase
    (CPH_Install.configuration input reservation).reserved (CPH_Install.configuration input reservation).query
    (CPH_Install.configuration input reservation).geometry (CPH_Install.configuration input reservation).stageBase
    (CPH_Install.configuration input reservation).finish (CPH_Install.configuration input reservation).boundaries
    (CPH_Install.configuration input reservation).std native1 native2 prepareOwner primitiveOwner hashv extraction
    prior sha256 H p1 syscall program data1 data2 slot state1 state2 final1 final2
    saved post1 post2 accepted1 accepted2 Par_Parameters.deployed root length

  have ⟨cuts,writer,reader,multiproof,scanY,checkY,scanned,tx1,batches,header2,header1,rest⟩ := base
  have sourceFacts := T2R_Parser.on_run _ _ _ _ _ _ _ _ _ _ _ _ _ run header1.2.2.1 scanned.2.2
  have acceptance := T2R_Nonvacuity.same_cuts L sdk copy std allocator e1 e2 w1 w2 admission1 admission2
    c native1 native2 prepareOwner primitiveOwner hashv extraction sha256 H p1 syscall
    program data1 data2 slot state1 state2 final1 final2 saved post1 post2 accepted1 accepted2
    f s cuts writer reader
  let version := CPG_History.on_cuts (game := oldGame)
    (c := DrvC_FirstConstants.configuration c) (keyLaw := keyLaw) (extraction := extraction)
    (std := std) (notSystem := programNotSystem) (accepted1 := accepted1) (accepted2 := accepted2)
    (RuntimePersistence := RuntimePersistence) (f := f) (s := s) (cuts := cuts)
  have writerKey : version.key = (e1.handles 2).1 := by
    change ((p.layout t).handles 2).1 = _
    rw [game.consecutive.2.1]
    rfl
  have readerKey : version.key = (e2.handles 6).1 := by
    change ((p.layout t).handles 2).1 = _
    rw [game.consecutive.2.2]
    exact game.checkpoint.1
  have events : version.events = p.physicalEvents t := by
    change (CPP_BankHistory.run native1 native2 copy allocator program
      (CPR_SourceBank.afterCopy (CPG_Projection.cached (p.bank t)) ((p.layout t).handles 2).1 saved) actions).2 = _
    exact congrArg Prod.snd (CPG_RuntimeTrace.result game.recorded.1.2.2)
  have strong := Rc2_Base.strengthen L e1 e2 w1 w2 _ _ _ _ _ _ _ _ reservation program
    data1 data2 slot saved post1 post2 H f s outer pre middle fs ss run base
  have initial := NP6_Constructors.on_run _ _ _ _ _ _ _ _ _ _ _ run
  refine ⟨f,s,outer,pre,middle,fs,ss,run,tx2,calls,strong,initial,publicFacts,sourceFacts,
    version,writerKey,readerKey,events,S2X.checkpoint_persistence _ _ version,?_,?_⟩
  · obtain ⟨i,pub,proof,tag,size,fit,yes⟩ := acceptance
    exact ⟨i,pub,proof,tag,size,fit,fun p2prime => yes version p2prime⟩
  · exact caller version

#print axioms accepted
end AspisR1.CPH_Pair
end
