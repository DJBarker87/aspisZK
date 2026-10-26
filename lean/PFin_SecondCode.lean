import F3U_SecondInstances
import F3S_BatchDictionary
set_option autoImplicit false
noncomputable section
namespace AspisR1.PFin_SecondCode
open Aeneas Aeneas.Std Result VTop_Stages

theorem common (base : Ops) (reserved : Bool)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (D : aspis_core.digest.Digest32 Unit)
    (pub proof ck : Slice U8) :
    GExq_SecondCode.common base reserved hashv D pub proof ck ()=
      GExp_SecondCode.common base reserved hashv D pub proof ck := by
  rw [F3U_SecondInstances.native,F3U_SecondInstances.retained]
  have batch : GExq_BatchSource.stage D () proof=SdkC_BatchSource.stageCode hashv proof :=
    funext (fun p=>funext (fun root=>F3S_BatchDictionary.stage hashv D proof p root))
  rw [batch]
  rfl

theorem same (base : Ops) (reserved : Bool)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (D : aspis_core.digest.Digest32 Unit)
    (pub proof ck : Slice U8) :
    GExq_SecondCode.code base reserved hashv D pub proof ck ()=
      GExp_SecondCode.code base reserved hashv D pub proof ck := by
  unfold GExq_SecondCode.code GExp_SecondCode.code
  rw [common]
  rfl

#print axioms common
#print axioms same
end AspisR1.PFin_SecondCode
end
