import IDb_Components
import FJu_Top
import FJu_GlobalOwners
import FJu_Result
import FJp_Top
import ARW_Induced
import FJp_Residual
import FJp_FinalObservations
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
namespace AspisR1.IDb_Deployed
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

/-- Full field inventory, with only the four unresolved inputs named.
This is a source-model family, not a closed runtime deployment certificate. -/
def deployedConfigurationFull {CoreError : Type}
    (adapter : AdapterRw.Ops) (currentBase : AspisR1CurrentCaller.Ops)
    (stageBase : VTop_Stages.Ops) (reserved : Bool)
    (indexError : CoreError) (reservation : NP6_StdModel.Reservation) :
    DrvC_Installation.Configuration FIo_Install.W CoreError :=
  FIq_Install.configuration indexError
    { adapter := adapter
      currentBase := currentBase
      stageBase := stageBase
      reserved := reserved
      query := IDb_Components.query
      geometry := IDb_Components.geometry indexError
      finish := IDa_Deployed.finish reservation
      boundaries := IDa_Deployed.boundaries reservation
      std := NP6_StdModel.calls reservation } reservation

section Fields
variable {C : Type} (adapter : AdapterRw.Ops) (currentBase : AspisR1CurrentCaller.Ops)
  (stageBase : VTop_Stages.Ops) (reserved : Bool) (err : C) (r : NP6_StdModel.Reservation)
local notation "cfg" => deployedConfigurationFull adapter currentBase stageBase reserved err r

theorem adapter_field : cfg.adapter =
    {adapter with op35:=fun e=>ok e,op36:=Hist_Authority.keyEq} := rfl

theorem current_field : cfg.currentBase = currentBase := rfl

theorem stage_field : cfg.stageBase = Port1_Library.install (Port1_Library.std stageBase) := rfl

theorem reserved_field : cfg.reserved = reserved := rfl

theorem query_field : cfg.query = IDb_Components.query := rfl

theorem geometry_field : cfg.geometry = IDb_Components.geometry err := rfl

theorem finish_field : cfg.finish = IDa_Deployed.finish r := rfl

theorem boundaries_field : cfg.boundaries = IDa_Deployed.boundaries r := rfl

theorem std_field : cfg.std = NP6_StdModel.calls r := rfl

/-- The top's further FIp selection preserves all these choices, fieldwise. -/
theorem top_fields :
    (FIp_Install.configuration err cfg r).adapter=cfg.adapter ∧
    (FIp_Install.configuration err cfg r).currentBase=cfg.currentBase ∧
    (FIp_Install.configuration err cfg r).stageBase=cfg.stageBase ∧
    (FIp_Install.configuration err cfg r).reserved=cfg.reserved ∧
    (FIp_Install.configuration err cfg r).query=cfg.query ∧
    (FIp_Install.configuration err cfg r).geometry=cfg.geometry ∧
    (FIp_Install.configuration err cfg r).finish=cfg.finish ∧
    (FIp_Install.configuration err cfg r).boundaries=cfg.boundaries ∧
    (FIp_Install.configuration err cfg r).std=cfg.std :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- An actually retained SDK callback, not selected by the installer. -/
theorem digest_residual : (DrvC_Installation.sdk cfg).op43=adapter.op43 := rfl

/-- The stage seed still supplies its canonical scan callback. -/
theorem stage_scan_residual : (DrvC_Installation.stage cfg).op4=stageBase.op4 := rfl

#print axioms adapter_field
#print axioms current_field
#print axioms stage_field
#print axioms reserved_field
#print axioms query_field
#print axioms geometry_field
#print axioms finish_field
#print axioms boundaries_field
#print axioms std_field
#print axioms top_fields
#print axioms digest_residual
#print axioms stage_scan_residual
end Fields

theorem FJu_Deployed {W A CoreError Tx : Type}
    (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A)
    (e1 e2 : Entry) (w1 w2 : W)
    (admission1 : RuntimeEntrypointAdmission L e1 w1 3)
    (admission2 : RuntimeEntrypointAdmission L e2 w2 7)
    (adapter : AdapterRw.Ops) (currentBase : AspisR1CurrentCaller.Ops)
    (stageBase : VTop_Stages.Ops) (reserved : Bool) (indexError : CoreError)
    (reservation : NP6_StdModel.Reservation)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk (FIp_Install.configuration indexError (deployedConfigurationFull adapter currentBase stageBase reserved indexError reservation) reservation)) native1 native2 hashv)
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
    (finishOwners : FJu_GlobalOwners.Owners
      (FIp_Install.configuration indexError (deployedConfigurationFull adapter currentBase stageBase reserved indexError reservation) reservation)
      (Rc2_Install.configuration (Rc5_Install.seed indexError (FIp_Install.select reservation (deployedConfigurationFull adapter currentBase stageBase reserved indexError reservation))) reservation).boundaries)
    :
    let P := ARW_Induced.program native1 copy allocator CPH_Program.verifier a;
    let runtime := ARX_AdmittedRuntime.runtime (Tx := Tx) L copy allocator (deployedConfigurationFull adapter currentBase stageBase reserved indexError reservation) indexError reservation native1 native2 hashv a;
    let select : F3X_Projection.Output → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs :=
      fun _ => P2P_NativeSelection.pair
        (DrvC_Installation.sdk (FIp_Install.configuration indexError (deployedConfigurationFull adapter currentBase stageBase reserved indexError reservation) reservation))
        CPH_Program.verifier e1 e2 data2 slot;
    MultiproofConeP6Frozen2Stage.P6Boundary (P6C_Extension.dictionary hashv H) () H
      Op5T_P6.parent Op5T_P6.parent Op5T_P6.parent MultiproofConeP6Batch.referenceLeaf ∧
    DrvC_Implementation.driver (FIp_Install.configuration indexError (deployedConfigurationFull adapter currentBase stageBase reserved indexError reservation) reservation) = DrvC_SourceEntry.source (FIp_Install.configuration indexError (deployedConfigurationFull adapter currentBase stageBase reserved indexError reservation) reservation) hashv ∧
    DrvC_Installation.sdk (FIp_Install.configuration indexError (deployedConfigurationFull adapter currentBase stageBase reserved indexError reservation) reservation) =
      SdkD_PairBatches.dictionary (FIp_Install.configuration indexError (deployedConfigurationFull adapter currentBase stageBase reserved indexError reservation) reservation).adapter (FIp_Install.configuration indexError (deployedConfigurationFull adapter currentBase stageBase reserved indexError reservation) reservation).currentBase (FIp_Install.configuration indexError (deployedConfigurationFull adapter currentBase stageBase reserved indexError reservation) reservation).stageBase
        (FIp_Install.configuration indexError (deployedConfigurationFull adapter currentBase stageBase reserved indexError reservation) reservation).finish (FIp_Install.configuration indexError (deployedConfigurationFull adapter currentBase stageBase reserved indexError reservation) reservation).reserved (FIp_Install.configuration indexError (deployedConfigurationFull adapter currentBase stageBase reserved indexError reservation) reservation).query (FIp_Install.configuration indexError (deployedConfigurationFull adapter currentBase stageBase reserved indexError reservation) reservation).geometry
        (FIp_Install.configuration indexError (deployedConfigurationFull adapter currentBase stageBase reserved indexError reservation) reservation).boundaries (FIp_Install.configuration indexError (deployedConfigurationFull adapter currentBase stageBase reserved indexError reservation) reservation).std ∧
    (FJu_Result.Outcome L e1 e2 w1 w2
      (FIp_Install.configuration indexError (deployedConfigurationFull adapter currentBase stageBase reserved indexError reservation) reservation).adapter (FIp_Install.configuration indexError (deployedConfigurationFull adapter currentBase stageBase reserved indexError reservation) reservation).currentBase
      (FIp_Install.configuration indexError (deployedConfigurationFull adapter currentBase stageBase reserved indexError reservation) reservation).reserved (FIp_Install.configuration indexError (deployedConfigurationFull adapter currentBase stageBase reserved indexError reservation) reservation).query
      (FIp_Install.configuration indexError (deployedConfigurationFull adapter currentBase stageBase reserved indexError reservation) reservation).geometry (FIp_Install.configuration indexError (deployedConfigurationFull adapter currentBase stageBase reserved indexError reservation) reservation).stageBase
      (FIp_Install.configuration indexError (deployedConfigurationFull adapter currentBase stageBase reserved indexError reservation) reservation).finish (FIp_Install.boundaries (deployedConfigurationFull adapter currentBase stageBase reserved indexError reservation).boundaries)
      reservation CPH_Program.verifier data1 data2 slot saved post1 post2 H
      (DrvC_Implementation.driver (FIp_Install.configuration indexError (deployedConfigurationFull adapter currentBase stageBase reserved indexError reservation) reservation)) prior
      (p.physicalEvents t) hashv
      (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965)
        (eval H (Hiq_RecordedJoint.program
          (F3X_Account.program (FIp_Install.configuration indexError (deployedConfigurationFull adapter currentBase stageBase reserved indexError reservation) reservation) hashv P)
          F3X_Projection.project select)))) ∧
    (F3X_ModelClaims.Claims (FIp_Install.configuration indexError (deployedConfigurationFull adapter currentBase stageBase reserved indexError reservation) reservation) D P (Q0+Q1) ∧
      F3Y_SourceClaims.Claims (FIp_Install.configuration indexError (deployedConfigurationFull adapter currentBase stageBase reserved indexError reservation) reservation) D hashv P (Q0+Q1) select ∧
      F3Y_AccountMass.Claims (FIp_Install.configuration indexError (deployedConfigurationFull adapter currentBase stageBase reserved indexError reservation) reservation) hashv P (Q0+Q1) select ∧
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
    Rc2_Events.Facts (FIp_Install.configuration indexError (deployedConfigurationFull adapter currentBase stageBase reserved indexError reservation) reservation) hashv native1 native2 copy allocator CPH_Program.verifier H saved ∧
    CPH_Protection.Facts p t saved CPH_Program.verifier ∧
    CPH_Trace.Facts p t u saved native1 native2 copy allocator CPH_Program.verifier ∧
    CPH_Recorder.Facts (FIp_Install.configuration indexError (deployedConfigurationFull adapter currentBase stageBase reserved indexError reservation) reservation) hashv native1 native2 copy allocator
      CPH_Program.verifier H p t u saved ∧
    S6N_Installation.Facts (DrvC_Installation.sdk (FIp_Install.configuration indexError (deployedConfigurationFull adapter currentBase stageBase reserved indexError reservation) reservation))
 := by
  exact FJu_Top.deployed L sdk copy std allocator e1 e2 w1 w2 admission1 admission2
    (deployedConfigurationFull adapter currentBase stageBase reserved indexError reservation)
    indexError reservation native1 native2 hashv extraction sha256 H p1 syscall
    data1 data2 slot state1 state2 final1 final2 saved post1 post2 accepted1 accepted2
    root length prior words p t u actions game RuntimePersistence D a Q0 Q1 queries finishOwners

#print axioms FJu_Deployed
end AspisR1.IDb_Deployed
end
