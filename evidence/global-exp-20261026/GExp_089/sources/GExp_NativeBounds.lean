import GExp_PartialCount
import GExp_SecondBudget
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExp_NativeBounds
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem first (base : AspisR1CurrentCaller.Ops)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Unit)
    (semantic : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256) (before : SdkC_Source.Log) :
    (SdkC_Source.run hashv (GExp_FirstCode.code base B std hashv D semantic pub proof split) before).2.length ≤
      before.length+11350 :=
  GExp_PartialCount.from_count _ _ (GExp_FirstBudget.first _ _ _ _ _ _ _ _ _)
    hashv sha256 H p1 syscall before

theorem second (base : VTop_Stages.Ops) (reserved : Bool)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : VTop_Stages.aspis_core.digest.Digest32 Unit) (pub proof ck : Slice U8)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256) (before : SdkC_Source.Log) :
    (SdkC_Source.run hashv (GExp_SecondCode.code base reserved hashv D pub proof ck) before).2.length ≤
      before.length+11235 :=
  GExp_PartialCount.from_count _ _ (GExp_SecondBudget.second _ _ _ _ _ _ _)
    hashv sha256 H p1 syscall before

#print axioms first
#print axioms second
end AspisR1.GExp_NativeBounds
end
