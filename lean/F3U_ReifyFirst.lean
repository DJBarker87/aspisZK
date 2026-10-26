import F3U_ReifyExact
import F3U_PairInputs
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3U_ReifyFirst
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open DrvC_Installation

theorem first {F C : Type} (c : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (semantic : Port1_Driver.Semantic) (pub proof : Slice U8) (H : Bytes → State)
    (accepted : (eval H (DrvC_PairProgram.source c hashv semantic pub proof)).2=true) :
    ∃ saved : alloc.vec.Vec U8,
      CheckpointBytes5Effect.erase (SdkC_Source.dictionary (F3U_Oracle.hashv H)) ()
        (GExp_FirstCode.code (GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry)
          c.boundaries c.std hashv (currentDigest c) (AspisS6CurrentVerifierCarrier.toPublic semantic)
          pub proof 10#usize)=ok (.Ok saved) ∧
      CheckpointBytes5Effect.erase (SdkC_Source.dictionary (F3U_Oracle.hashv H)) ()
        (GExp_SecondCode.code (stage c) c.reserved hashv (digest c) pub proof saved.deref)=ok (.Ok ()) := by
  obtain ⟨saved,first,second⟩ := F3U_PairInputs.accepted c hashv semantic pub proof H accepted
  exact ⟨saved,(F3U_ReifyValue.value _ H).symm.trans first,(F3U_ReifyValue.value _ H).symm.trans second⟩

#print axioms first
end AspisR1.F3U_ReifyFirst
end
