import RPz7_F3U_SecondSkeleton
import RPz7_GExp_SecondCode
import RPz7_GExq_SecondCode
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3U_SecondInstances
open Aeneas Aeneas.Std Result VTop_Stages

theorem native (base : Ops) (reserved : Bool)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (D : aspis_core.digest.Digest32 Unit)
    (pub proof checkpoint : Slice U8) :
    GExq_SecondCode.common base reserved hashv D pub proof checkpoint ()=
      F3U_SecondSkeleton.common base reserved hashv D pub proof checkpoint
        (GExq_RetainedReader.code reserved checkpoint proof pub .S2)
        (GExq_BatchSource.stage D () proof) := rfl
#print axioms native

theorem retained (base : Ops) (reserved : Bool)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (D : aspis_core.digest.Digest32 Unit)
    (pub proof checkpoint : Slice U8) :
    GExp_SecondCode.common base reserved hashv D pub proof checkpoint=
      F3U_SecondSkeleton.common base reserved hashv D pub proof checkpoint
        (GExp_RetainedReader.code reserved checkpoint proof pub .S2)
        (SdkC_BatchSource.stageCode hashv proof) := rfl
#print axioms retained
end AspisR1.F3U_SecondInstances
end
