import F3U_ReifyFirst
import F3V_FirstCode
import F3V_SecondComplete
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3V_PairLog
open Aeneas Aeneas.Std Result
open DrvC_Installation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

theorem evaluated {F C : Type} (c : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (semantic : Port1_Driver.Semantic) (pub proof : Slice U8) (H : Bytes → State)
    (accepted : (eval H (DrvC_PairProgram.source c hashv semantic pub proof)).2=true) :
    ∃ saved : alloc.vec.Vec U8,
      eval H (DrvC_PairProgram.source c hashv semantic pub proof)=
        (SdkC_Source.readLog (SdkC_Source.run (F3U_Oracle.hashv H)
          (GExp_FirstCode.code (GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry)
            c.boundaries c.std hashv (currentDigest c) (AspisS6CurrentVerifierCarrier.toPublic semantic)
            pub proof 10#usize) []).2 ++
         SdkC_Source.readLog (SdkC_Source.run (F3U_Oracle.hashv H)
          (GExp_SecondCode.code (stage c) c.reserved hashv (digest c) pub proof saved.deref) []).2,true) := by
  obtain ⟨saved,first,second⟩ := F3U_PairInputs.accepted c hashv semantic pub proof H accepted
  refine ⟨saved,?_⟩
  have one := F3U_ReifyExact.exact
    (GExp_FirstCode.code (GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry)
      c.boundaries c.std hashv (currentDigest c) (AspisS6CurrentVerifierCarrier.toPublic semantic) pub proof 10#usize) H
  have two := F3U_ReifyExact.exact
    (GExp_SecondCode.code (stage c) c.reserved hashv (digest c) pub proof saved.deref) H
  have oneValue := (congrArg Prod.snd one).symm.trans first
  have twoValue := (congrArg Prod.snd two).symm.trans second
  dsimp only at oneValue twoValue
  rw [oneValue] at one
  rw [twoValue] at two
  simp only [DrvC_PairProgram.source,GExp_Experiment.first,GExp_Experiment.second,eval_bind,
    one,two,Port1_Driver.verdict,eval,List.append_nil]
  rfl

#print axioms evaluated
end AspisR1.F3V_PairLog
end
