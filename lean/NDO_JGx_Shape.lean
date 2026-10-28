import NDO_JFx_HeaderFields
import RPz7_Tx2I_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_Shape
open Aeneas Aeneas.Std Result
attribute [local irreducible] JFx_NativeBytes.proof

theorem source : Tx2I_Install.shape JFx_NativeBytes.proof=ok (.Ok .S2) := by
  have accepted := JFx_HeaderFields.shape_accepted
  unfold Op3I_Install.sourceBody at accepted
  obtain ⟨r,call,rest⟩ := Op3I_ParseLaws.bind_success _ _ _ accepted
  cases r with
  | Err e => cases rest
  | Ok v =>
    obtain ⟨rfl,fields⟩ := Op3I_ParseLaws.source_success JFx_NativeBytes.proof v call
    simp only [Tx2I_Install.shape,call,bind_tc_ok,Tx2I_Install.variant]
#print axioms source
end AspisR1.JGx_Shape
end
