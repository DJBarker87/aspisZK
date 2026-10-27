import Aeneas
set_option autoImplicit false
namespace AspisR1.FJk_MaskNonzero
open Aeneas Aeneas.Std
/-- Isolate the word fact from the dependent whole-execution context. -/
theorem positive (mask : U16) (h : (mask != 0#u16)=true) : mask.val≠0 := by
  intro z
  have eq : mask=0#u16 := UScalar.eq_of_val_eq z
  have f : (mask != 0#u16)=false := by rw [eq];rfl
  exact Bool.noConfusion (f.symm.trans h)
#print axioms positive
end AspisR1.FJk_MaskNonzero
