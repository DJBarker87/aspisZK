import F3V_SecondCode
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3V_SecondComplete
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem same (H : Bytes → State) (base : VTop_Stages.Ops) (reserved : Bool)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : VTop_Stages.aspis_core.digest.Digest32 Unit) (pub proof ck : Slice U8) :
    GExp_SecondCode.code base reserved hashv D pub proof ck=
      GExp_SecondCode.code base reserved (F3U_Oracle.hashv H) (F3V_StageDictionary.ideal H D) pub proof ck := by
  unfold GExp_SecondCode.code
  rw [F3V_SecondCode.common H base reserved hashv D]
  rfl

#print axioms same
end AspisR1.F3V_SecondComplete
end
