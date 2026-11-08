import NNH_DigestProgramStatus
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_DigestSyntaxSlots
open Aeneas Aeneas.Std Result

theorem first {Hash : Type} (base : AspisR1CurrentCaller.Ops)
 (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
 (h1 h2 : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash)
 (semantic : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (pub proof : Slice U8) (split : Usize) (hash : Hash) :
 GExq_FirstCode.code base B std h1 D semantic pub proof split hash =
 GExq_FirstCode.code base B std h2 D semantic pub proof split hash := by
 unfold GExq_FirstCode.code
 rfl

theorem common {Hash : Type} (base : VTop_Stages.Ops) (reserved : Bool)
 (h1 h2 : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (pub proof ck : Slice U8) (hash : Hash) :
 GExq_SecondCode.common base reserved h1 D pub proof ck hash =
 GExq_SecondCode.common base reserved h2 D pub proof ck hash := by
 unfold GExq_SecondCode.common
 rfl

theorem second {Hash : Type} (base : VTop_Stages.Ops) (reserved : Bool)
 (h1 h2 : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (pub proof ck : Slice U8) (hash : Hash) :
 GExq_SecondCode.code base reserved h1 D pub proof ck hash =
 GExq_SecondCode.code base reserved h2 D pub proof ck hash := by
 unfold GExq_SecondCode.code
 rw [common base reserved h1 h2]
#print axioms first
#print axioms common
#print axioms second
end AspisR1.NNH_DigestSyntaxSlots
end
