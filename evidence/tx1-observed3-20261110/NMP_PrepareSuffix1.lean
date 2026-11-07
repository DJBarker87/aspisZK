import NMP_PrepareSuffix2
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_PrepareSuffix
open Aeneas Aeneas.Std Result NMP_prepare NMP_Emitted NMP_PrepareSteps
open NMT_CallTree (erase)
/-- One source call and the already-compiled suffix; no whole-state unfolding. -/
theorem fold1 {H W : Type} (c : Calls) (s : Parent H W) (logical : alloc.vec.Vec U8) :
 erase (execute c 7 (.split s logical)) = f1 c s logical := by
 rw [execute]
 simp only [NMP_PrepareSteps.step,Bind.bind,Pure.pure,NMT_CallTree.erase_bind,NMT_CallTree.erase_invoke,NMT_CallTree.erase_pure,NMT_CallTree.erase_lift,NMT_CallTree.erase,NMT_CallTree.result_assoc,NMT_CallTree.result_right,NMP_DirectBind.ok,NMP_DirectBind.fail,NMP_DirectBind.div,fold2,f1]
 repeat' first
 | rfl
 | (apply NMT_CallTree.result_congr; intro x; simp only [NMP_PrepareSteps.step,Bind.bind,Pure.pure,NMT_CallTree.erase_bind,NMT_CallTree.erase_invoke,NMT_CallTree.erase_pure,NMT_CallTree.erase_lift,NMT_CallTree.erase,NMT_CallTree.result_assoc,NMT_CallTree.result_right,NMP_DirectBind.ok,NMP_DirectBind.fail,NMP_DirectBind.div,fold2,f1])
 | (split <;> simp only [NMP_PrepareSteps.step,Bind.bind,Pure.pure,NMT_CallTree.erase_bind,NMT_CallTree.erase_invoke,NMT_CallTree.erase_pure,NMT_CallTree.erase_lift,NMT_CallTree.erase,NMT_CallTree.result_assoc,NMT_CallTree.result_right,NMP_DirectBind.ok,NMP_DirectBind.fail,NMP_DirectBind.div,fold2,f1])
#print axioms fold1
end AspisR1.NMP_PrepareSuffix
