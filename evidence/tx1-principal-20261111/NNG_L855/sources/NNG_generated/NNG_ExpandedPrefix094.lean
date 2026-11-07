import LIBC_ExpandSemanticModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ExpandedPrefix094
open Aeneas Aeneas.Std
/-- A symbolic first32-window proof; the13,831-cell constructor stays an
abstract ofFn and no concrete payload/recurrence is evaluated. -/
theorem first32 (input : Slice U8) (bound : 32 ≤ input.val.length) :
 (LIBC_ExpandSemanticModel.output input).val.take 32=input.val.take 32 := by
 have length : ((LIBC_ExpandSemanticModel.output input).val.take 32).length=32 := by
  simp only [LIBC_ExpandSemanticModel.output,List.length_take,List.length_ofFn]
  rfl
 apply List.ext_getElem
 · rw [length,List.length_take,Nat.min_eq_left bound]
 · intro i hi hj
   rw [length] at hi
   have live : i<13831 := by omega
   have original : i < input.val.length := by omega
   simp only [LIBC_ExpandSemanticModel.output,List.getElem_take,List.getElem_ofFn]
   unfold LIBC_ExpandSemanticModel.byte
   rw [dif_pos hi,List.getElem?_eq_getElem original]
   rfl
#print axioms first32
end AspisR1.NNG_ExpandedPrefix094
