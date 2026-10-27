import RPv_FJh_Base
set_option autoImplicit false
namespace AspisR1.FJh_Fin16Indices
open Aeneas Aeneas.Std
theorem zero : (⟨(0#usize).val,by decide⟩ : Fin (16#usize).val)=(0 : Fin 16) := by
  apply Fin.ext
  scalar_tac
theorem one : (⟨1,by decide⟩ : Fin (16#usize).val)=(1 : Fin 16) := by
  apply Fin.ext
  rfl
theorem nine : (⟨9,by decide⟩ : Fin (16#usize).val)=(9 : Fin 16) := by
  apply Fin.ext
  rfl
theorem ten : (⟨10,by decide⟩ : Fin (16#usize).val)=(10 : Fin 16) := by
  apply Fin.ext
  rfl
#print axioms zero
#print axioms one
#print axioms nine
#print axioms ten
end AspisR1.FJh_Fin16Indices
