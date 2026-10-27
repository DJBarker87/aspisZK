import ARX_Root
import FIq_Install
import S1SemanticRootCopyV1
import ARW_Induced
import ARX_Residual
import ARW_Observations
import Rc10_Top
import ART_Runtime
import FIs_Top
import Rc9_Top
import S6N_Installation
import Rc8_Top
import Rc9_Install
import FIp_Install
import FIp_Core
import FIo_Nonvacuity
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.IDa_Deployed
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

/-- Only records without a complete installed component remain data inputs.
Overwritten slots in these records have no effect on the selected dictionary. -/
structure Uninstalled (CoreError : Type) where
  adapter : AdapterRw.Ops
  currentBase : AspisR1CurrentCaller.Ops
  stageBase : VTop_Stages.Ops
  reserved : Bool
  query : Port3_NativeQueryBody.Ops
  geometry : Port3_NativeGeometryBody.Ops CoreError

/-- Complete finish interpretation: FIo/FIn value bodies and Port3 release leaves.
No success, acceptance or semantic law is stored in this record. -/
def finish (reservation : NP6_StdModel.Reservation) :
    AspisR1Stage2.Stage2Finish.FinishOps FIo_Install.W where
  field := FIn_Primitives.field
  quarter := ok 536870912#u32
  add := FIn_Primitives.add
  mulM := SAG_StageScale.mulM
  ne := Port3_FinishStage.ne
  polynomial := FIn_ExtractInstall.polynomial
  trace := fun _ _ _ => ok ()
  folds := Port3_FinishStage.folds
  newWeights := FIn_WeightsInstall.newWeights
  pair := FIo_Install.pair reservation
  mark := Port3_QueryStage.mark
  dot := SAG_DotClosed.source

/-- Source interpretations of every semantic finish boundary. Root-copy has
its existing accepted-value/panic interpretation; std effects remain a P6 gate. -/
def boundaries (reservation : NP6_StdModel.Reservation) :
    AspisR1PublicPreparation.FinishModel.Boundaries where
  fromFn := OraclePortStdBuilder.fromFn
  mask := FIp_SemanticArithmetic.mask
  add := FIp_SemanticArithmetic.add
  mul := FIp_SemanticArithmetic.mul
  terminal := FIq_Terminal.terminal
  circle := F3M_CircleSource.source
  unwrapRoot := AspisR1PublicPreparation.S1SemanticRootCopy.unwrapRoot
  claims := ClaimsUnrolledFinish.claims (NP6_StdModel.calls reservation)

def seed {CoreError : Type} (missing : Uninstalled CoreError)
    (reservation : NP6_StdModel.Reservation) :
    DrvC_Installation.Configuration FIo_Install.W CoreError where
  adapter := missing.adapter
  currentBase := missing.currentBase
  stageBase := missing.stageBase
  finish := finish reservation
  reserved := missing.reserved
  query := missing.query
  geometry := missing.geometry
  boundaries := boundaries reservation
  std := NP6_StdModel.calls reservation

/-- Explicit partial source installation, not a source-to-ELF certificate.
All unresolved outer components are exposed in `missing`. -/
def deployedConfiguration {CoreError : Type} (missing : Uninstalled CoreError)
    (indexError : CoreError) (reservation : NP6_StdModel.Reservation) :
    DrvC_Installation.Configuration FIo_Install.W CoreError :=
  FIq_Install.configuration indexError (seed missing reservation) reservation

/-- Projection checks avoid reducing the unused outer records. -/
theorem selected_fields {CoreError : Type} (missing : Uninstalled CoreError)
    (indexError : CoreError) (reservation : NP6_StdModel.Reservation) :
    (FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation).finish =
      finish reservation ∧
    (FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation).boundaries =
      boundaries reservation ∧
    (FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation).std =
      NP6_StdModel.calls reservation := ⟨rfl,rfl,rfl⟩

theorem terminal_fixed {CoreError : Type} (missing : Uninstalled CoreError)
    (indexError : CoreError) (reservation : NP6_StdModel.Reservation) :
    (deployedConfiguration missing indexError reservation).boundaries.terminal =
      FIq_Terminal.terminal := rfl

theorem finish_fixed {CoreError : Type} (missing : Uninstalled CoreError)
    (indexError : CoreError) (reservation : NP6_StdModel.Reservation) :
    (deployedConfiguration missing indexError reservation).finish = finish reservation := rfl

theorem boundaries_fixed {CoreError : Type} (missing : Uninstalled CoreError)
    (indexError : CoreError) (reservation : NP6_StdModel.Reservation) :
    (deployedConfiguration missing indexError reservation).boundaries = boundaries reservation := rfl

theorem ARX_Deployed {W A CoreError Tx : Type}
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
    (finishOwners : FIp_GlobalOwners.Owners
      (FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation)
      (Rc2_Install.configuration (Rc5_Install.seed indexError (FIp_Install.select reservation (deployedConfiguration missing indexError reservation))) reservation).boundaries)
    :
    let P := ARW_Induced.program native1 copy allocator CPH_Program.verifier a;
    let runtime := ARX_AdmittedRuntime.runtime (Tx := Tx) L copy allocator (deployedConfiguration missing indexError reservation) indexError reservation native1 native2 hashv a;
    let select : F3X_Projection.Output → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs :=
      fun _ => P2P_NativeSelection.pair
        (DrvC_Installation.sdk (FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation))
        CPH_Program.verifier e1 e2 data2 slot;
    MultiproofConeP6Frozen2Stage.P6Boundary (P6C_Extension.dictionary hashv H) () H
      Op5T_P6.parent Op5T_P6.parent Op5T_P6.parent MultiproofConeP6Batch.referenceLeaf ∧
    DrvC_Implementation.driver (FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation) = DrvC_SourceEntry.source (FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation) hashv ∧
    DrvC_Installation.sdk (FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation) =
      SdkD_PairBatches.dictionary (FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation).adapter (FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation).currentBase (FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation).stageBase
        (FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation).finish (FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation).reserved (FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation).query (FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation).geometry
        (FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation).boundaries (FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation).std ∧
    (FIs_Result.Outcome L e1 e2 w1 w2
      (FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation).adapter (FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation).currentBase
      (FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation).reserved (FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation).query
      (FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation).geometry (FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation).stageBase
      (FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation).finish (FIp_Install.boundaries (deployedConfiguration missing indexError reservation).boundaries)
      reservation CPH_Program.verifier data1 data2 slot saved post1 post2 H
      (DrvC_Implementation.driver (FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation)) prior
      (p.physicalEvents t) hashv
      (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965)
        (eval H (Hiq_RecordedJoint.program
          (F3X_Account.program (FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation) hashv P)
          F3X_Projection.project select)))) ∧
    (F3X_ModelClaims.Claims (FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation) D P (Q0+Q1) ∧
      F3Y_SourceClaims.Claims (FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation) D hashv P (Q0+Q1) select ∧
      F3Y_AccountMass.Claims (FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation) hashv P (Q0+Q1) select ∧
      F3T_RuntimeBound.failureModel runtime ≤ F3T_Numeric.total (Q0+Q1) ∧
      (Q0+Q1 ≤ F3U_RangeEdges.maxQueries →
        F3T_RuntimeBound.failureModel runtime ≤ (Q0+Q1+1:Rat)*(1/(2:Rat)^100)) ∧
      (Q0+Q1=0 → F3U_Numeric.margin ≤ 1/(2:Rat)^100-F3T_RuntimeBound.failureModel runtime ∧
        F3T_RuntimeBound.failureModel runtime < 1/(2:Rat)^100)) ∧
    (native1 CPH_Program.verifier e1.first data1 = ok (.Ok saved) ∧
      saved.val.length = 1768 ∧
      payloadBytes encode (post1.payload (e1.heap.accounts 2).1) 1768 = bytesOf saved.val ∧
      post1.ambient = e1.heap.ambient ∧ post1.accounts = e1.heap.accounts ∧
      post1.counter = e1.heap.counter ∧
      (∀ cell, cell ≠ (e1.heap.accounts 2).1 → post1.payload cell = e1.heap.payload cell)) ∧
    Rc2_Events.Facts (FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation) hashv native1 native2 copy allocator CPH_Program.verifier H saved ∧
    CPH_Protection.Facts p t saved CPH_Program.verifier ∧
    CPH_Trace.Facts p t u saved native1 native2 copy allocator CPH_Program.verifier ∧
    CPH_Recorder.Facts (FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation) hashv native1 native2 copy allocator
      CPH_Program.verifier H p t u saved ∧
    S6N_Installation.Facts (DrvC_Installation.sdk (FIp_Install.configuration indexError (deployedConfiguration missing indexError reservation) reservation))
 := by
  exact ARX_Root.deployed L sdk copy std allocator e1 e2 w1 w2 admission1 admission2
    (deployedConfiguration missing indexError reservation) indexError reservation
    native1 native2 hashv extraction sha256 H p1 syscall data1 data2 slot
    state1 state2 final1 final2 saved post1 post2 accepted1 accepted2 root length
    prior words p t u actions game RuntimePersistence D a Q0 Q1 queries finishOwners

#print axioms selected_fields
#print axioms terminal_fixed
#print axioms finish_fixed
#print axioms boundaries_fixed
#print axioms ARX_Deployed
set_option pp.universes true in
set_option pp.all true in
#check @ARX_Deployed
end AspisR1.IDa_Deployed
end
