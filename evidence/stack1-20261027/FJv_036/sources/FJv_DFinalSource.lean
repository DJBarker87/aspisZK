import FJv_DNativePair
import FJv_DDefinitions
import T2R_Nonvacuity
import FJt_GlobalTerminal
import IDa_Deployed
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
namespace AspisR1.FJv_DFinalSource
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

theorem source {W A CoreError Tx : Type}
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
 :
    FJv_DFinalResult.Outcome L e1 e2 w1 w2
      (FJt_GlobalTerminal.configuration missing indexError reservation).adapter
      (FJt_GlobalTerminal.configuration missing indexError reservation).currentBase
      (FJt_GlobalTerminal.configuration missing indexError reservation).reserved
      (FJt_GlobalTerminal.configuration missing indexError reservation).query
      (FJt_GlobalTerminal.configuration missing indexError reservation).geometry
      (FJt_GlobalTerminal.configuration missing indexError reservation).stageBase
      (FJt_GlobalTerminal.configuration missing indexError reservation).finish
      (IDa_Deployed.boundaries reservation) reservation CPH_Program.verifier data1 data2 slot saved post1 post2 H
      (DrvC_Implementation.driver (FJt_GlobalTerminal.configuration missing indexError reservation)) prior := by
  let c:=FJt_GlobalTerminal.configuration missing indexError reservation
  have installed : c.finish=FIn_Install.finishOps c.finish := by
    rfl
  obtain ⟨f,s,outer,pre,middle,fs,ss,run,tx2,origin,calls,base,selected,publicFacts,caller⟩:=
    FJv_DNativePair.accepted L sdk copy std allocator e1 e2 w1 w2 admission1 admission2
      missing indexError reservation (IDa_Deployed.boundaries reservation)
      c.std native1 native2 (SAQ_Decoder.primitives (FIp_Install.select reservation
        (IDa_Deployed.deployedConfiguration missing indexError reservation)).query)
      hashv extraction prior sha256 H p1 syscall CPH_Program.verifier data1 data2 slot state1 state2 final1 final2
      saved post1 post2 accepted1 accepted2 Par_Parameters.deployed root length words
  have cuts:=base.1
  have ⟨cuts0,writer,reader,multiproof,scanY,checkY,scanned,tx1,batches,header2,header1,rest⟩:=base
  have sourceFacts:=T2R_Parser.on_run _ _ _ _ _ _ _ _ _ _ _ _ _ run header1.2.2.1 scanned.2.2
  have strong:=Rc2_Base.strengthen L e1 e2 w1 w2 _ _ _ _ _ _ _ _ reservation CPH_Program.verifier
    data1 data2 slot saved post1 post2 H f s outer pre middle fs ss run base
  have initial:=NP6_Constructors.on_run _ _ _ _ _ _ _ _ _ _ _ run
  have acceptance:=T2R_Nonvacuity.same_cuts L sdk copy std allocator e1 e2 w1 w2 admission1 admission2 c native1 native2
    (SAP_PrepareOwner.installed _ (IDa_Deployed.boundaries reservation) c.std)
    (SAQ_Decoder.primitives (FIp_Install.select reservation
      (IDa_Deployed.deployedConfiguration missing indexError reservation)).query)
    hashv extraction sha256 H p1 syscall CPH_Program.verifier data1 data2 slot state1 state2 final1 final2
    saved post1 post2 accepted1 accepted2 f s cuts base.2.1 base.2.2.1
  exact ⟨f,s,outer,pre,middle,fs,ss,run,tx2,origin,calls,strong,initial,selected,publicFacts,sourceFacts,acceptance,
    Rc3_Nonvacuity.derive _ _ _ _ _ _ _ _ acceptance,caller⟩
#print axioms source
end AspisR1.FJv_DFinalSource
end
