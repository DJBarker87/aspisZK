import F3U_SourceInputs
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3U_PairInputs
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open AspisV8R19.OracleProgramOps
open DrvC_Installation

theorem accepted {F C : Type} (c : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (semantic : Port1_Driver.Semantic) (pub proof : Slice U8) (H : Bytes → State)
    (accepted : (eval H (DrvC_PairProgram.source c hashv semantic pub proof)).2=true) :
    ∃ saved : alloc.vec.Vec U8,
      (eval H (GExp_Experiment.first (GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry)
        c.boundaries c.std hashv (currentDigest c) ⟨AspisS6CurrentVerifierCarrier.toPublic semantic,pub,proof,10#usize⟩)).2=ok (.Ok saved) ∧
      (eval H (GExp_Experiment.second (stage c) c.reserved hashv (digest c) ⟨pub,proof,saved.deref⟩)).2=ok (.Ok ()) := by
  unfold DrvC_PairProgram.source at accepted
  simp only [eval_bind] at accepted
  cases first : (eval H (GExp_Experiment.first
      (GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry) c.boundaries c.std hashv (currentDigest c)
      ⟨AspisS6CurrentVerifierCarrier.toPublic semantic,pub,proof,10#usize⟩)).2 with
  | fail e => simp only [first,eval] at accepted;cases accepted
  | div => simp only [first,eval] at accepted;cases accepted
  | ok reply => cases reply with
    | Err e => simp only [first,eval] at accepted;cases accepted
    | Ok saved =>
      refine ⟨saved,rfl,?_⟩
      simp only [first,eval_bind,eval] at accepted
      cases second : (eval H (GExp_Experiment.second (stage c) c.reserved hashv (digest c) ⟨pub,proof,saved.deref⟩)).2 with
      | fail e => simp only [second,Port1_Driver.verdict] at accepted;cases accepted
      | div => simp only [second,Port1_Driver.verdict] at accepted;cases accepted
      | ok reply => cases reply with
        | Err e => simp only [second,Port1_Driver.verdict] at accepted;cases accepted
        | Ok unit => cases unit;rfl

#print axioms accepted
end AspisR1.F3U_PairInputs
end
