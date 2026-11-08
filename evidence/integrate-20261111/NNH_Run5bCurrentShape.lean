import NNH_Run5bHost
import NNH_Stage1NativePublic
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_Run5bCurrentShape
open Aeneas Aeneas.Std Result NNH_Libraries
variable (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
abbrev current := DrvC_Installation.currentInstalled (NNH_CorrectConfiguration.configuration m env err r)

theorem slot (proof : Slice U8) :
 (current m env err r).op3 proof = Op3I_Install.sourceBody proof := rfl

theorem parse (proof : Slice U8)
 (success : LIB_VLib.parseShapeValue (LIB_Carriers.bytes proof) env = .ok ()) :
 ∃ variant, (current m env err r).op3 proof = .ok (.Ok variant) := by
 change LIBC_ResultGraph.value LIBC_ParseShape.port (.error .Parse)
  (LIBC_ParseShape.model (LIB_Carriers.bytes proof) env) = .ok () at success
 unfold LIBC_ParseShape.model at success
 rw [LIBC_Bytes.from_native] at success
 rw [slot]
 unfold Op3I_Install.sourceBody
 cases hp : Op3I_Source.verifier.candidate.parse_shape Op3I_Std.ops proof with
 | fail e => simp only [hp,LIBC_ResultGraph.value] at success; cases success
 | div => simp only [hp,LIBC_ResultGraph.value] at success; cases success
 | ok reply => cases reply with
  | Err e =>
   simp only [hp,LIBC_ResultGraph.value,LIBC_ParseShape.port] at success
   cases success
  | Ok variant =>
   exact ⟨Op3I_Install.currentVariant variant,by rfl⟩
#print axioms slot
#print axioms parse
end AspisR1.NNH_Run5bCurrentShape
end
