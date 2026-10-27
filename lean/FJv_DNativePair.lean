import FJp_RetPrefix
import FJt_GlobalTerminal
import FJv_DDefinitions
import FJv_DLiteral
/- FIs same-run enrichment; read-only source: P2P_ActualPair.lean. -/
import P2P_Origin
import FIs_P2P_PairSelected
import FIs_P2P_ActualResult
/- New-prefix accepted-only consumer; source of origin: lean/SAP_ActualPair.lean. -/
import SAF_C_SAP_PairSelected
import SAF_C_SAP_ActualResult
import SAF_C_SAP_SourceConsumer
import SAP_PrepareOwner
import SAP_NativePair
import SAF_C_SAP_ResultSelected
import T2Nat_NativePair
import AuS1_Accepted
import DrvC_SourceHeadline
import Cons_Ten
import SAF_C_Cons_Finish
import Cons_Native
import Cons_Continuation
import Cons_Base
import Cons_Caller
import Cons_Result
import T2R_ResultSource
import SAF_C_T2R_Finish
import Cons_NativeBuild
import SAF_C_Cons_FinishProof
import FIs_Cons_Second
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
namespace AspisR1.FJv_DNativePair
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

/-- The union of Op4P, Tx2I, Op5T and Tx1Q conclusions on one f,s,cuts.
Success-conditioned marks retain rejected-prefix effect obligations. -/
theorem accepted {W A M Cv CoreError : Type} {N : Nat}
    (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A)
    (e1 e2 : Entry) (w1 w2 : W)
    (admission1 : RuntimeEntrypointAdmission L e1 w1 3)
    (admission2 : RuntimeEntrypointAdmission L e2 w2 7)
    (missing : IDa_Deployed.Uninstalled CoreError) (err : CoreError) (r : NP6_StdModel.Reservation)
    (seed : AspisR1PublicPreparation.FinishModel.Boundaries)
    (claimsStd : ClaimsUnrolledFinish.StdCalls) (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (primitiveOwner : Port5Q1_QueryPorts.SessionAPrimitives (FJt_GlobalTerminal.configuration missing err r).query)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (sdkOps (Tx2I_Install.install (FJt_GlobalTerminal.configuration missing err r).adapter (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base (FJt_GlobalTerminal.configuration missing err r).stageBase) (FJt_GlobalTerminal.configuration missing err r).reserved (FJt_GlobalTerminal.configuration missing err r).query (FJt_GlobalTerminal.configuration missing err r).geometry)) (FJt_GlobalTerminal.configuration missing err r).finish) (Uni_Install.current (FJt_GlobalTerminal.configuration missing err r).currentBase (FJt_GlobalTerminal.configuration missing err r).reserved (FJt_GlobalTerminal.configuration missing err r).query (FJt_GlobalTerminal.configuration missing err r).geometry) (F3M_CircleSource.install (FIq_Install.boundaries seed)) claimsStd) native1 native2 hashv)
    (prior : Program Bytes State Unit)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (program : S2W_ExtractionBoundary.Program) (data1 data2 : Slice U8)
    (slot : S2W_ExtractionBoundary.Slot) (state1 state2 final1 final2 : A)
    (saved : alloc.vec.Vec U8) (post1 post2 : Heap (Nat → Record))
    (accepted1 : S2W_D189Wrappers.first native1 copy allocator e1 program data1 state1 =
      ok (.Ok (saved,post1,final1)))
    (accepted2 : S2W_D189Wrappers.second native2 allocator e2 program data2 slot state2 =
      ok (.Ok (post2,final2)))
    (p : FS2.Duplex.Params M Cv N) (root : Array U8 32#usize) (length : U32)
    (words : CanonicalCutEnrichedTranscript.Words)
 :
    FJv_DPairResult.Outcome L e1 e2 w1 w2 (FJt_GlobalTerminal.configuration missing err r).adapter (FJt_GlobalTerminal.configuration missing err r).currentBase (FJt_GlobalTerminal.configuration missing err r).reserved (FJt_GlobalTerminal.configuration missing err r).query (FJt_GlobalTerminal.configuration missing err r).geometry (FJt_GlobalTerminal.configuration missing err r).stageBase (FJt_GlobalTerminal.configuration missing err r).finish (FIq_Install.boundaries seed) claimsStd program data1 data2 slot saved post1 post2 H prior := by
  have prepareOwner : WAdm_Domain.SessionAPrepare
      (Tx1Q_Execution.actual (Op5T_Concrete.current (FJt_GlobalTerminal.configuration missing err r).currentBase) (FJt_GlobalTerminal.configuration missing err r).reserved (FJt_GlobalTerminal.configuration missing err r).query (FJt_GlobalTerminal.configuration missing err r).geometry
        (F3M_CircleSource.install (FIq_Install.boundaries seed)) claimsStd) :=
    SAP_PrepareOwner.installed
      (Tx1Q_SameCut.dictionary (Op5T_Concrete.current (FJt_GlobalTerminal.configuration missing err r).currentBase) (FJt_GlobalTerminal.configuration missing err r).reserved (FJt_GlobalTerminal.configuration missing err r).query (FJt_GlobalTerminal.configuration missing err r).geometry) (FIq_Install.boundaries seed) claimsStd
  obtain ⟨f,s,outer,pre,middle,fs,ss,run,rootBinding,tx2,origin,calls,base,selected,publicFacts,caller⟩ :=
    FJp_Ret_PairSelected.accepted L sdk copy std allocator e1 e2 w1 w2 admission1 admission2
      (FJt_GlobalTerminal.configuration missing err r).adapter (FJt_GlobalTerminal.configuration missing err r).currentBase (FJt_GlobalTerminal.configuration missing err r).reserved (FJt_GlobalTerminal.configuration missing err r).query (FJt_GlobalTerminal.configuration missing err r).geometry (FJt_GlobalTerminal.configuration missing err r).stageBase (FJt_GlobalTerminal.configuration missing err r).finish (F3M_CircleSource.install (FIq_Install.boundaries seed))
      claimsStd native1 native2 prepareOwner primitiveOwner hashv extraction prior sha256 H p1 syscall
      program data1 data2 slot state1 state2 final1 final2 saved post1 post2 accepted1 accepted2 p root length
  have ⟨cuts,writer,reader,multiproof,scanY,checkY,scanned,tx1,batches,header2,header1,rest⟩ := base
  have pairCuts : SourceCuts (SdkD_PairBatches.dictionary (FJt_GlobalTerminal.configuration missing err r).adapter (FJt_GlobalTerminal.configuration missing err r).currentBase (FJt_GlobalTerminal.configuration missing err r).stageBase (FJt_GlobalTerminal.configuration missing err r).finish
      (FJt_GlobalTerminal.configuration missing err r).reserved (FJt_GlobalTerminal.configuration missing err r).query (FJt_GlobalTerminal.configuration missing err r).geometry (F3M_CircleSource.install (FIq_Install.boundaries seed)) claimsStd) e1.first (e2.second secondSizes) saved f s := by
    rw [AuS1_Install.dictionary]; exact cuts
  have pairExtraction : S2W_DigestExtraction.AeneasExtraction
      (SdkD_PairBatches.dictionary (FJt_GlobalTerminal.configuration missing err r).adapter (FJt_GlobalTerminal.configuration missing err r).currentBase (FJt_GlobalTerminal.configuration missing err r).stageBase (FJt_GlobalTerminal.configuration missing err r).finish (FJt_GlobalTerminal.configuration missing err r).reserved (FJt_GlobalTerminal.configuration missing err r).query (FJt_GlobalTerminal.configuration missing err r).geometry
        (F3M_CircleSource.install (FIq_Install.boundaries seed)) claimsStd) native1 native2 hashv := by
    rw [AuS1_Install.dictionary]; exact extraction
  refine ⟨f,s,outer,pre,middle,fs,ss,run,tx2,origin,calls,base,selected,publicFacts,?_⟩
  intro history p2prime entry
  obtain ⟨parsed,facts,sites,continuation⟩ := caller history p2prime entry
  refine ⟨parsed,facts,sites,?_⟩
  intro queryLeaves geoLeaves domain multiply one inverse
  obtain ⟨authParsed,frame,parser,frameRead,target,ten,finish⟩ :=
    continuation queryLeaves geoLeaves domain multiply one inverse
  obtain ⟨version,key,ledger,events,sameCheckpoint,sameProof,samePub,savedLength⟩ :=
    RowOrder_History.on_d189_cuts copy std allocator e1 e2 _ native1 native2 hashv extraction
      program data1 state1 final1 saved post1 accepted1 f s cuts CPhy_Header.decode H writer reader history p2prime
  obtain ⟨rootView,rootRange,rootCopy⟩ := rootBinding
  obtain ⟨newFrame,newRead,newTarget,auth⟩ := AuS1_OnRun.same_pair prior
    (FJt_GlobalTerminal.configuration missing err r).adapter (FJt_GlobalTerminal.configuration missing err r).currentBase (FJt_GlobalTerminal.configuration missing err r).stageBase (FJt_GlobalTerminal.configuration missing err r).finish
    (FJt_GlobalTerminal.configuration missing err r).reserved (FJt_GlobalTerminal.configuration missing err r).query (FJt_GlobalTerminal.configuration missing err r).geometry (F3M_CircleSource.install (FIq_Install.boundaries seed)) claimsStd
    native1 native2 hashv pairExtraction sha256 H p1 syscall e1.first (e2.second secondSizes)
    saved f s pairCuts sameCheckpoint sameProof authParsed parser run rootView rootRange rootCopy
  refine ⟨authParsed,frame,parser,frameRead,target,?_⟩
  refine FJv_DLiteral.from_cut missing err r seed claimsStd
    e1.first (e2.second secondSizes) saved f s pairCuts selected run header1.2.2.1 H
    native1 native2 hashv pairExtraction sha256 p1 syscall words scanned.2.2 _ authParsed parser
    sameProof.symm tx2 ten finish queryLeaves geoLeaves domain multiply one inverse _ () calls
    sameCheckpoint ?_
  intro data rho q prepared
  rcases auth data rho q prepared with hit | indexed
  · exact Or.inl hit
  · exact Or.inr ⟨OraclePortAllSelectedRecoveryC6.recovered _ newFrame authParsed 2,indexed⟩
#print axioms accepted
end AspisR1.FJv_DNativePair
end
