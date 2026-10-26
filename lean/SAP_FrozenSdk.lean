import SAP_FrozenSource
import SAP_PairSelected
import SAP_ActualResult
import SAP_SourceConsumer
import SAP_PrepareOwner
import SAP_NativePair
import SAP_ResultSelected
import T2Nat_NativePair
import AuS1_Accepted
import DrvC_SourceHeadline
import Cons_Ten
import Cons_Finish
import Cons_Native
import Cons_Continuation
import Cons_Base
import Cons_Caller
import Cons_Result
import T2R_ResultSource
import T2R_Finish
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
namespace AspisR1.SAP_FrozenSdk
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
theorem accepted {W A M Cv F CoreError : Type} {N : Nat}
    (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (std : TrustedStd copy) (allocator : Allocator A)
    (e1 e2 : Entry) (w1 w2 : W)
    (admission1 : RuntimeEntrypointAdmission L e1 w1 3)
    (admission2 : RuntimeEntrypointAdmission L e2 w2 7)
    (adapterOps : AdapterRw.Ops) (ops : Ops)
    (reserved : Bool) (queryOps : Port3_NativeQueryBody.Ops)
    (geoOps : Port3_NativeGeometryBody.Ops CoreError)
    (stageBase : VTop_Stages.Ops) (finishOps : AspisR1Stage2.Stage2Finish.FinishOps F)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (claimsStd : ClaimsUnrolledFinish.StdCalls) (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (primitiveOwner : Port5Q1_QueryPorts.SessionAPrimitives queryOps)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction (sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stageBase) reserved queryOps geoOps)) finishOps) (Uni_Install.current ops reserved queryOps geoOps) (F3M_CircleSource.install B) claimsStd) native1 native2 hashv)
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
    (words : CanonicalCutEnrichedTranscript.Words)
    (canonical : Port5Q1_GeometryCanonical.SessionAPrimitives geoOps)
    (domain : Port5Q1_Domain.SessionADomain geoOps)
    (multiply : geoOps.op9=AspisR1Qm31ArithmeticProbe.field.M31.mul)
    (one : geoOps.op7=ok (1#u32)) (inverse : geoOps.op11=Port4C_InverseExecution.inverse_owned)
    (decoder : LiteralByteProtocol.Decoder) :
    ∃ f s log,
      SourceCuts (SdkD_PairBatches.dictionary adapterOps ops stageBase finishOps reserved queryOps geoOps (F3M_CircleSource.install B) claimsStd)
        e1.first (e2.second secondSizes) saved f s ∧ RawJ_RecordCuts.Recorded f s saved log ∧
    ∃ run : Tx1Q_Execution.Run (Tx1Q_Execution.actual (Op5T_Concrete.current ops) reserved queryOps geoOps (F3M_CircleSource.install B) claimsStd)
      reserved queryOps geoOps (SdkD_PairBatches.current adapterOps ops stageBase finishOps reserved queryOps geoOps (F3M_CircleSource.install B) claimsStd) ()
      (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.pub f.proof f.split saved,
    ∃ (i : F3_Model.Input) (p : OraclePortCompactDraft.Parsed) (q : Fin 22 → Fin 262144)
      (input : RecordedBinaryExperimentBin.SourceInputs) (tx2 : Cons_Native.Witness),
      i.physical.bytes=bytesOf f.pub.val ∧ i.stored=bytesOf f.proof.val ∧
      Cons_Native.Calls (AuS1_Install.base stageBase) finishOps reserved queryOps geoOps
        (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32
          (SdkD_PairBatches.dictionary adapterOps ops stageBase finishOps reserved queryOps geoOps (F3M_CircleSource.install B) claimsStd)) ()
        s.pub s.proof s.checkpoint tx2 ∧
      ∀ (decode : S2W_AuthenticatedInputs.HeaderDecode)
        (writerJoin : S2W_AuthenticatedInputs.CheckpointWriterConeJoin (SdkD_PairBatches.dictionary adapterOps ops stageBase finishOps reserved queryOps geoOps (F3M_CircleSource.install B) claimsStd) decode H f.semantic f.pub f.proof f.split)
        (readerJoin : S2W_AuthenticatedInputs.CheckpointReaderConeJoin (SdkD_PairBatches.dictionary adapterOps ops stageBase finishOps reserved queryOps geoOps (F3M_CircleSource.install B) claimsStd) decode H s.pub s.proof s.checkpoint)
        (history : S2X.CheckpointVersionBinding (bytesOf saved.val) (bytesOf s.checkpoint.val))
        (p2prime : S2W_AuthenticatedInputs.P2Prime H f.proof f.pub s.proof s.pub)
        (prior : AspisV8R19.MemoizedProgramLaw.Program Bytes State Unit)
        (x : F3S_FinishWitness.Primitives finishOps tx2.v2 tx2.p2
          {tx2.returned2 with weights:=tx2.back2 tx2.flushed2})
        (leaves : F3T_Leaves.Holds finishOps tx2.v2 tx2.p2
          {tx2.returned2 with weights:=tx2.back2 tx2.flushed2} x q p
          (LiteralTranscript.erasePrefix (AspisV8R19.MemoizedProgramLaw.eval H
            (F3J_SamplerRun.program i.proof 0 33 (FS.emptyPrefix i.semantic.value))).2) input),
        let trace := (AspisV8R19.MemoizedProgramLaw.eval H prior).1 ++
          AuS1_Recovery.log (Uni_Install.current ops reserved queryOps geoOps) (F3M_CircleSource.install B) claimsStd
            (SdkD_PairBatches.current adapterOps ops stageBase finishOps reserved queryOps geoOps (F3M_CircleSource.install B) claimsStd)
            (AspisS6CurrentVerifierCarrier.toPublic f.semantic) f.proof () (Array.repeat 29#usize run.zero)
        AuS1_Finish.Collision H trace p q ∨
        ((AspisV8R19.MemoizedProgramLaw.eval H (GExq_CallerRecord.program adapterOps ops (AuS1_Install.base stageBase)
          finishOps reserved queryOps geoOps (F3M_CircleSource.install B) claimsStd hashv program e1.first (e2.second secondSizes) data1 data2 slot)).1=
          (AspisV8R19.MemoizedProgramLaw.eval H (F3_Model.verifier decoder i)).1 ∧
         (AspisV8R19.MemoizedProgramLaw.eval H (F3_Model.verifier decoder i)).2=true) := by
  obtain ⟨owned1,written⟩ := S2W_D189Wrappers.first_accepted native1 copy std allocator e1 program
    data1 state1 final1 saved post1 accepted1
  obtain ⟨owned2,unchanged⟩ := S2W_D189Wrappers.second_accepted native2 allocator e2 program
    data2 slot state2 final2 post2 accepted2
  have pairExtraction : S2W_DigestExtraction.AeneasExtraction
      (SdkD_PairBatches.dictionary adapterOps ops stageBase finishOps reserved queryOps geoOps
        (F3M_CircleSource.install B) claimsStd) native1 native2 hashv := by
    rw [AuS1_Install.dictionary]; exact extraction
  exact SAP_FrozenSource.accepted_pair adapterOps ops stageBase finishOps reserved queryOps geoOps B claimsStd
    native1 native2 hashv pairExtraction program e1.first (e2.second secondSizes) data1 data2 slot saved owned1 owned2
    sha256 H p1 syscall words primitiveOwner canonical domain multiply one inverse decoder

#print axioms accepted
end AspisR1.SAP_FrozenSdk
end
