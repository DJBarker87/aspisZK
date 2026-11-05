import NHV_NativeOps
set_option autoImplicit false
noncomputable section
namespace NHV_ReleaseOps
open Aeneas Aeneas.Std Result
abbrev Phase := VTop_Stages.verifier.Phase
/-- Exact source marker semantics. Native credit is restricted to deployed None;
no function-pointer value or Some observer is used by the native certificates. -/
def mark (obs : Option (Phase → Result Unit)) (phase : Phase) : Result Unit :=
 match obs with
 | none => ok ()
 | some callback => callback phase

def installed (base : VTop_Stages.Ops) (qbase : AspisR1.Port3_NativeQueryBody.Ops)
 (qPlace gPlace : Nat) (reserved : Bool) : VTop_Stages.Ops :=
 NHV_NativeOps.installed {base with op13:=mark} qbase qPlace gPlace reserved

theorem source (base : VTop_Stages.Ops) (qbase : AspisR1.Port3_NativeQueryBody.Ops)
 (qPlace gPlace : Nat) (reserved : Bool)
 {H : Type} (D : VTop_Stages.aspis_core.digest.Digest32 H)
 (pub proof checkpoint : Aeneas.Std.Slice Aeneas.Std.U8) (hash : H) :
 NHT_EmittedCommon.tx2_common (installed base qbase qPlace gPlace reserved)
   D pub proof checkpoint hash none =
 VTop_Stages.verifier.candidate.tx2_common (installed base qbase qPlace gPlace reserved)
   D pub proof checkpoint hash none :=
 NHV_NativeOps.source {base with op13:=mark} qbase qPlace gPlace reserved
   D pub proof checkpoint hash none

theorem release_mark (base : VTop_Stages.Ops) (qbase : AspisR1.Port3_NativeQueryBody.Ops)
 (qPlace gPlace : Nat) (reserved : Bool) (phase : Phase) :
 (installed base qbase qPlace gPlace reserved).op13 none phase=ok () := rfl

/-- Missing native callee laws are retained verbatim, not replaced by success. -/
theorem open_fields (base : VTop_Stages.Ops) (qbase : AspisR1.Port3_NativeQueryBody.Ops)
 (qPlace gPlace : Nat) (reserved : Bool) :
 @VTop_Stages.Ops.op18 (installed base qbase qPlace gPlace reserved)=@VTop_Stages.Ops.op18 base ∧
 @VTop_Stages.Ops.op5 (installed base qbase qPlace gPlace reserved)=@VTop_Stages.Ops.op5 base ∧
 (installed base qbase qPlace gPlace reserved).op19=base.op19 := ⟨rfl,rfl,rfl⟩
#print axioms source
#print axioms release_mark
#print axioms open_fields
end NHV_ReleaseOps
