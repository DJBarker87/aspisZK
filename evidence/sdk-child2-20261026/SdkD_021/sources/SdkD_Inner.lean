import Tx2N_Accepted
import Uni_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkD_Inner
open Aeneas Aeneas.Std Result
open S2W_NativeConsolidation S2W_D189Entry S2W_D189Wrappers S2W_TrustedStd S2Trust
open S2W_AuthenticatedInputs
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- The Tx2N reader/inner conclusion on exactly the Uni source cuts. -/
theorem same_pair {A F CoreError : Type}
    (copy : Heap (Nat → Record) → Nat → Payload → Outcome (Nat → Record))
    (stdCopy : TrustedStd copy) (allocator : Allocator A) (e1 e2 : Entry)
    (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (ClaimsUnrolledSdk.sdkOps
        (Tx2I_Install.install adapter (Op5T_Concrete.stage (Tx2N_Execution.control stage reserved query geo)) finish)
        (Uni_Install.current ops reserved query geo) B std) native1 native2 hashv)
    (program : S2W_ExtractionBoundary.Program) (data1 : Slice U8) (state1 final1 : A)
    (saved : alloc.vec.Vec U8) (post1 : Heap (Nat → Record))
    (accepted1 : first native1 copy allocator e1 program data1 state1 = .ok (.Ok (saved,post1,final1)))
    (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts (ClaimsUnrolledSdk.sdkOps
        (Tx2I_Install.install adapter (Op5T_Concrete.stage (Tx2N_Execution.control stage reserved query geo)) finish)
        (Uni_Install.current ops reserved query geo) B std) e1.first (e2.second secondSizes) saved f s)
    (decode : HeaderDecode) (H : Bytes → State)
    (writer : CheckpointWriterConeJoin (ClaimsUnrolledSdk.sdkOps
        (Tx2I_Install.install adapter (Op5T_Concrete.stage (Tx2N_Execution.control stage reserved query geo)) finish)
        (Uni_Install.current ops reserved query geo) B std) decode H f.semantic f.pub f.proof f.split)
    (reader : CheckpointReaderConeJoin (ClaimsUnrolledSdk.sdkOps
        (Tx2I_Install.install adapter (Op5T_Concrete.stage (Tx2N_Execution.control stage reserved query geo)) finish)
        (Uni_Install.current ops reserved query geo) B std) decode H s.pub s.proof s.checkpoint)
    (runtime : S2X.CheckpointVersionBinding
      (S2W_EntryWriteHistory.payloadBytes S2W_ReturnedCheckpoint.encode (post1.payload (e1.heap.accounts 2).1) 1768)
      (MultiproofConeCanonical.bytesOf s.checkpoint.val))
    (p2prime : P2Prime H f.proof f.pub s.proof s.pub)
    (queryLeaves : Port5Q1_QueryPorts.SessionAPrimitives query)
    (geoLeaves : Port5Q1_GeometryCanonical.SessionAPrimitives geo)
    (domain : Port5Q1_Domain.SessionADomain geo)
    (multiply : geo.op9 = AspisR1Qm31ArithmeticProbe.field.M31.mul)
    (one : geo.op7 = ok 1#u32) (inverse : geo.op11 = Port4C_InverseExecution.inverse_owned) :
    Tx2N_Finish.Outcome finish reserved query
      (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32
        (ClaimsUnrolledSdk.sdkOps
          (Tx2I_Install.install adapter (Op5T_Concrete.stage (Tx2N_Execution.control stage reserved query geo)) finish)
          (Uni_Install.current ops reserved query geo) B std)) () s.pub s.proof s.checkpoint saved H
      (MultiproofConeCanonical.bytesOf f.proof.val) (MultiproofConeCanonical.bytesOf f.pub.val) := by
  obtain ⟨version,key,ledger,events,checkpoint,proof,pub,size⟩ :=
    RowOrder_History.on_d189_cuts copy stdCopy allocator e1 e2 _ native1 native2 hashv
      extraction program data1 state1 final1 saved post1 accepted1 f s cuts decode H
      writer reader runtime p2prime
  apply Tx2N_Finish.accepted (Op5T_Concrete.stage stage) finish reserved query queryLeaves geo
    geoLeaves domain multiply one inverse _ () s.pub s.proof s.checkpoint saved H
    (MultiproofConeCanonical.bytesOf f.proof.val) (MultiproofConeCanonical.bytesOf f.pub.val) checkpoint
  exact cuts.second

#print axioms same_pair
end AspisR1.SdkD_Inner
end
