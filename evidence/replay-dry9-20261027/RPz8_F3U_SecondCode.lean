import RPz8_F3U_ReaderCode
import RPz7_F3U_SecondInstances
import RPz7_F3S_BatchDictionary
import RPz7_GExq_SecondCode
import RPz7_GExp_SecondCode
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3U_SecondCode
open Aeneas Aeneas.Std Result VTop_Stages

theorem common (base : Ops) (reserved : Bool)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (D : aspis_core.digest.Digest32 Unit)
    (pub proof checkpoint : Slice U8) :
    GExq_SecondCode.common base reserved hashv D pub proof checkpoint ()=
      GExp_SecondCode.common base reserved hashv D pub proof checkpoint := by
  rw [F3U_SecondInstances.native,F3U_SecondInstances.retained,F3U_ReaderCode.same]
  have batch : GExq_BatchSource.stage D () proof=SdkC_BatchSource.stageCode hashv proof := by
    funext p root
    exact F3S_BatchDictionary.stage hashv D proof p root
  rw [batch]

theorem same (base : Ops) (reserved : Bool)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (D : aspis_core.digest.Digest32 Unit)
    (pub proof checkpoint : Slice U8) :
    GExq_SecondCode.code base reserved hashv D pub proof checkpoint ()=
      GExp_SecondCode.code base reserved hashv D pub proof checkpoint := by
  simp only [GExq_SecondCode.code,GExp_SecondCode.code,common]
  rfl

#print axioms common
#print axioms same
end AspisR1.F3U_SecondCode
end
