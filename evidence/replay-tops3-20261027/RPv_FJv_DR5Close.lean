import RPv_FJv_DDefinitions
import RPv_FJv_DCaller
/- FIs same-run enrichment; read-only source: P2P_R5Close.lean. -/
import P2P_Origin
import RPv_FJv_DDefinitions
import RPv_FJv_DCaller
import RPz7_Rc5_Install
import RPz7_Rc5_Result
import RPz7_SAF_C_SAF_FinalResult
import RPz7_Rc2_Result
import RPz7_CPH_Game
import RPz7_CPH_Install
import RPz7_CPH_Result
import RPz7_CPG_History
import RPz7_CPR_PhysicalResult
import RPz7_CPG_Result
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
import RPz7_FIs_Cons_Second
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
namespace AspisR1.FJv_DR5Close
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

theorem from_saf {W A F CoreError Tx : Type}
    (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A)
    (e1 e2 : Entry) (w1 w2 : W)
    (admission1 : RuntimeEntrypointAdmission L e1 w1 3)
    (admission2 : RuntimeEntrypointAdmission L e2 w2 7)
    (input : DrvC_Installation.Configuration F CoreError) (indexError : CoreError)
    (reservation : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk (Rc5_Install.configuration indexError input reservation)) native1 native2 hashv)
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
    (RuntimePersistence : CPR_DataPersistence.TwoTransactionLaw
      (CPG_Projection.adjacent p) (CPG_Projection.ordinary p system) (CPG_Projection.before p)
      (CPG_Projection.tentative p)
      (CPG_Projection.success p) (CPG_Projection.loaded p))
    (original :
    FJv_DFinalResult.Outcome L e1 e2 w1 w2
      (Rc5_Install.configuration indexError input reservation).adapter (Rc5_Install.configuration indexError input reservation).currentBase
      (Rc5_Install.configuration indexError input reservation).reserved (Rc5_Install.configuration indexError input reservation).query
      (Rc5_Install.configuration indexError input reservation).geometry (Rc5_Install.configuration indexError input reservation).stageBase
      (Rc5_Install.configuration indexError input reservation).finish input.boundaries
      reservation program data1 data2 slot saved post1 post2 H
      (DrvC_Implementation.driver (Rc5_Install.configuration indexError input reservation)) prior) :
    FJv_DR5Result.Outcome L e1 e2 w1 w2
      (Rc5_Install.configuration indexError input reservation).adapter (Rc5_Install.configuration indexError input reservation).currentBase
      (Rc5_Install.configuration indexError input reservation).reserved (Rc5_Install.configuration indexError input reservation).query
      (Rc5_Install.configuration indexError input reservation).geometry (Rc5_Install.configuration indexError input reservation).stageBase
      (Rc5_Install.configuration indexError input reservation).finish input.boundaries
      reservation program data1 data2 slot saved post1 post2 H
      (DrvC_Implementation.driver (Rc5_Install.configuration indexError input reservation)) prior
      (p.physicalEvents t) := by
  let c := Rc5_Install.seed indexError input
  have keyLaw := Rc5_Install.key indexError input reservation
  have oldGame := CPH_Game.recordedInstance game
  obtain ⟨f,s,outer,pre,middle,fs,ss,run,tx2,origin,calls,base,initial,selected,publicFacts,sourceFacts,
    acceptance,nonvacuity,caller⟩ := original
  have cuts := base.1
  let version := CPG_History.on_cuts (game := oldGame)
    (c := Rc5_Install.configuration indexError input reservation) (keyLaw := keyLaw) (extraction := extraction)
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
  have owner : WAdm_Domain.SessionAPrepare
      (Tx1Q_Execution.actual (Op5T_Concrete.current (Rc5_Install.configuration indexError input reservation).currentBase)
        (Rc5_Install.configuration indexError input reservation).reserved
        (Rc5_Install.configuration indexError input reservation).query
        (Rc5_Install.configuration indexError input reservation).geometry
        (F3M_CircleSource.install input.boundaries) (NP6_StdModel.calls reservation)) :=
    SAP_PrepareOwner.installed _ input.boundaries (NP6_StdModel.calls reservation)
  have ports := SAQ_Decoder.primitives input.query
  have oracle : CheckpointBytes5Inputs.Oracle (VTop_Checkpoint.digest (Tx1Q_Install.digest
      (SdkD_PairBatches.current (Rc5_Install.configuration indexError input reservation).adapter
        (Rc5_Install.configuration indexError input reservation).currentBase
        (Rc5_Install.configuration indexError input reservation).stageBase
        (Rc5_Install.configuration indexError input reservation).finish
        (Rc5_Install.configuration indexError input reservation).reserved
        (Rc5_Install.configuration indexError input reservation).query
        (Rc5_Install.configuration indexError input reservation).geometry
        (F3M_CircleSource.install input.boundaries) (NP6_StdModel.calls reservation)))) () H := by
    intro parts digest returned
    change (DrvC_Installation.sdk (Rc5_Install.configuration indexError input reservation)).op43 () parts=ok digest at returned
    rw [extraction.digestSource,S2W_DigestExtraction.digest_eq_hashv] at returned
    exact (syscall.returningValue parts digest returned).trans (p1.realization _)
  have encoding := Rc4_Encoding.derive _ _ _ _ _ () _ _ _ _ _ run owner ports H oracle
  refine ⟨f,s,outer,pre,middle,fs,ss,run,tx2,origin,calls,encoding,base,initial,selected,TxS_RawPublic.of_typed f.pub f.proof publicFacts,sourceFacts,
    version,writerKey,readerKey,events,S2X.checkpoint_persistence _ _ version,?_,?_,?_⟩
  · obtain ⟨i,pub,proof,tag,size,fit,yes⟩ := acceptance
    exact ⟨i,pub,proof,tag,size,fit,fun p2prime => yes version p2prime⟩
  · exact nonvacuity version
  · exact FJv_DCaller.strengthen L e1 e2 w1 w2 _ _ _ _ _ _ _ input.boundaries
      (NP6_StdModel.calls reservation) program data1 data2 slot saved post1 post2 H
      f s outer pre middle fs ss run prior tx2 indexError input.query input.geometry rfl rfl version caller

#print axioms from_saf
end AspisR1.FJv_DR5Close
end
