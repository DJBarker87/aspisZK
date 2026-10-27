import P2P_Result
import Rc10_Caller
import FIs_Result
import FIs_Caller
import FIs_P2P_Result
import P2P_Caller
import P2P_Acceptance
import P2P_Origin
import P2P_R5Result
import Rc5_Result
import Rc6_Caller
import PFin_Packet
import P6C_FullBoundary
import CPP_Acceptance
import Rc4_Encoding
import SAP_PrepareOwner
import Rc3_Result
import Rc5_Caller
import TxS_RawPublic
import Rc5_Nonvacuity
import Rc2_Base
import T2R_Parser
import T2R_Acceptance
import T2Nat_NativePair
import AuS1_Accepted
import DrvC_SourceHeadline
import T2R_Ten
import T2R_Finish
import Cons_Native
import T2R_ContSource
import Cons_Base
import T2R_CallerSource
import T2R_PublicDecode
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
namespace AspisR1.Rc10_Result
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

theorem forget {W F CoreError : Type}
    (L : Library W (Nat → Record)) (e1 e2 : Entry) (w1 w2 : W)
    (adapterOps : AdapterRw.Ops) (ops : Ops) (reserved : Bool)
    (queryOps : Port3_NativeQueryBody.Ops) (geoOps : Port3_NativeGeometryBody.Ops CoreError)
    (stageBase : VTop_Stages.Ops) (finishOps : AspisR1Stage2.Stage2Finish.FinishOps F)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (reservation : NP6_StdModel.Reservation)
    (program : S2W_ExtractionBoundary.Program) (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot)
    (saved : alloc.vec.Vec U8) (post1 post2 : Heap (Nat → Record))
    (H : Bytes → State)
    (driver : OraclePortStoredExperimentC4.Input → Program Bytes State Bool)
    (prior : Program Bytes State Unit) (events : List S2X.AccountEvent)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest) (bad : Prop)
    (source : FIs_Result.Outcome L e1 e2 w1 w2 adapterOps ops reserved queryOps geoOps stageBase finishOps B reservation program data1 data2 slot saved post1 post2 H driver prior events hashv bad) :
    P2P_Result.Outcome L e1 e2 w1 w2 adapterOps ops reserved queryOps geoOps stageBase finishOps B reservation program data1 data2 slot saved post1 post2 H driver prior events hashv bad := by
  obtain ⟨f,s,outer,pre,middle,fs,ss,run,tx2,origin,enriched,encoding,base,initial,selected,publicFacts,parser,
    version,writerKey,readerKey,physical,persistent,packet,safe,whole,branch⟩ := source
  refine ⟨f,s,outer,pre,middle,fs,ss,run,tx2,origin,enriched,encoding,base,initial,selected,publicFacts,parser,
    version,writerKey,readerKey,physical,persistent,packet,safe,whole,?_⟩
  rcases branch with hit | good
  · exact Or.inl hit
  · obtain ⟨accepted,nonrejecting,caller⟩ := good
    exact Or.inr ⟨accepted,nonrejecting,(by apply Rc10_Caller.forget; exact caller)⟩

#print axioms forget
end AspisR1.Rc10_Result
end
