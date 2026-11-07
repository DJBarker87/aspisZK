import NMP_PrepareSuffix3
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_PrepareSuffix
open Aeneas Aeneas.Std Result NMP_prepare NMP_Emitted NMP_PrepareSteps
open NMT_CallTree (erase)
/-- One source call and the already-compiled suffix; no whole-state unfolding. -/
theorem fold2 {H W : Type} (c : Calls) (s : Parent H W) (semantic y1 : Slice U8) (back : SplitBack) (vecBack : VecBack) :
 erase (execute c 6 (.semantic s semantic y1 back vecBack)) = f2 c s semantic y1 back vecBack := by
 rw [execute]
 simp only [NMP_PrepareSteps.step,Bind.bind,Pure.pure,NMT_CallTree.erase_bind,NMT_CallTree.erase_invoke,NMT_CallTree.erase_pure,NMT_CallTree.erase_lift,NMT_CallTree.erase,NMT_CallTree.result_assoc,NMT_CallTree.result_right,NMP_DirectBind.ok,NMP_DirectBind.fail,NMP_DirectBind.div,fold3,f2]
 repeat' first
 | rfl
 | (apply NMT_CallTree.result_congr; intro x; simp only [NMP_PrepareSteps.step,Bind.bind,Pure.pure,NMT_CallTree.erase_bind,NMT_CallTree.erase_invoke,NMT_CallTree.erase_pure,NMT_CallTree.erase_lift,NMT_CallTree.erase,NMT_CallTree.result_assoc,NMT_CallTree.result_right,NMP_DirectBind.ok,NMP_DirectBind.fail,NMP_DirectBind.div,fold3,f2])
 | (split <;> simp only [NMP_PrepareSteps.step,Bind.bind,Pure.pure,NMT_CallTree.erase_bind,NMT_CallTree.erase_invoke,NMT_CallTree.erase_pure,NMT_CallTree.erase_lift,NMT_CallTree.erase,NMT_CallTree.result_assoc,NMT_CallTree.result_right,NMP_DirectBind.ok,NMP_DirectBind.fail,NMP_DirectBind.div,fold3,f2])
#print axioms fold2
end AspisR1.NMP_PrepareSuffix
