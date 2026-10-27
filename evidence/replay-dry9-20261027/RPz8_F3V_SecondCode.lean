import RPz7_F3U_SecondInstances
import RPz8_F3V_StageDictionary
import RPz8_F3V_StageBatch
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3V_SecondCode
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem common (H : Bytes → State) (base : VTop_Stages.Ops) (reserved : Bool)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : VTop_Stages.aspis_core.digest.Digest32 Unit) (pub proof ck : Slice U8) :
    GExp_SecondCode.common base reserved hashv D pub proof ck=
      GExp_SecondCode.common base reserved (F3U_Oracle.hashv H) (F3V_StageDictionary.ideal H D) pub proof ck := by
  simp only [F3U_SecondInstances.retained]
  have batch : SdkC_BatchSource.stageCode hashv proof=
      SdkC_BatchSource.stageCode (F3U_Oracle.hashv H) proof :=
    funext (fun _=>funext (fun _=>F3V_StageBatch.same _ _ _ _ _))
  rw [batch]
  rfl

#print axioms common
end AspisR1.F3V_SecondCode
end
