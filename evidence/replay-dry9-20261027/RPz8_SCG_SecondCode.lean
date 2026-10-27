import RPz8_SCG_BatchCode
import RPz7_GExq_SecondCode
import RPz7_GExp_SecondCode
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCG_SecondCode
open Aeneas Aeneas.Std Result VTop_Stages

theorem common (base : Ops) (reserved : Bool)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : aspis_core.digest.Digest32 Unit) (pub proof ck : Slice U8) :
    GExq_SecondCode.common base reserved hashv D pub proof ck () =
      GExp_SecondCode.common base reserved hashv D pub proof ck := by
  unfold GExq_SecondCode.common GExp_SecondCode.common
  simp only [SCG_BatchCode.stage D () hashv]
  rfl

theorem code (base : Ops) (reserved : Bool)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : aspis_core.digest.Digest32 Unit) (pub proof ck : Slice U8) :
    GExq_SecondCode.code base reserved hashv D pub proof ck () =
      GExp_SecondCode.code base reserved hashv D pub proof ck := by
  unfold GExq_SecondCode.code GExp_SecondCode.code
  simp only [common]
  rfl

#print axioms common
#print axioms code
end AspisR1.SCG_SecondCode
end
