import R1Z.PV_Src_RootFieldMeaning
import R1Z.PV_Src_PortParent
set_option autoImplicit false
namespace R1Z.PV_Src_RootZero
open Aeneas Aeneas.Std Result R0Z.WriterRefine BuilderForestAdmissionPort
abbrev zero := Array.repeat 8#usize aspis_core.field.M31.ZERO

theorem canonical : Canon8 zero := by
  intro j hj
  interval_cases j <;> simp only [zero,Array.repeat,aspis_core.field.M31.ZERO] <;> decide

theorem meaning : (fun i : Fin 8 => liftU (K := ZMod 2147483647) zero.val[i.val]!) = fun _ => 0 := by
  funext i
  fin_cases i <;> simp only [zero,Array.repeat,aspis_core.field.M31.ZERO,liftU] <;> rfl

#print axioms canonical
#print axioms meaning
end R1Z.PV_Src_RootZero
