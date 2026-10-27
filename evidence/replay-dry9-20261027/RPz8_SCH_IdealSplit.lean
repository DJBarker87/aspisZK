import RPz8_SCH_FirstChild
set_option autoImplicit false
namespace AspisR1.SCH_IdealSplit
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

theorem split (base : AspisR1CurrentCaller.Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Unit)
    (semantic : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (k : Usize) (saved : alloc.vec.Vec U8) (H : Bytes → State)
    (accepted : (eval H (SdkC_Oracle.program (GExq_FirstCode.code base B std hashv D semantic pub proof k ()))).2 =
      ok (.Ok saved)) : k = 10#usize := by
  by_contra different
  have reject : (k != AspisR1CurrentCaller.compact.SPLIT) = true := by
    simpa only [AspisR1CurrentCaller.compact.SPLIT,bne_iff_ne] using different
  unfold GExq_FirstCode.code at accepted
  simp only [reject,ite_true,SdkC_Oracle.program,eval] at accepted
  cases accepted

#print axioms split
end AspisR1.SCH_IdealSplit
