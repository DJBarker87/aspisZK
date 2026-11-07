import NMP_PrepareSuffix4
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_PrepareSuffix
open Aeneas Aeneas.Std Result NMP_prepare NMP_Emitted NMP_PrepareSteps
open NMT_CallTree (erase)
/-- One source call and the already-compiled suffix; no whole-state unfolding. -/
theorem fold3 {H W : Type} (c : Calls) (s : Parent H W) (semantic y1 : Slice U8) (back : SplitBack) (vecBack : VecBack) :
 erase (execute c 5 (.values s semantic y1 back vecBack)) = f3 c s semantic y1 back vecBack := by
 rw [execute]
 simp only [NMP_PrepareSteps.step,Bind.bind,Pure.pure,NMT_CallTree.erase_bind,NMT_CallTree.erase_invoke,NMT_CallTree.erase_pure,NMT_CallTree.erase_lift,NMT_CallTree.erase,NMT_CallTree.result_assoc,NMT_CallTree.result_right,NMP_DirectBind.ok,NMP_DirectBind.fail,NMP_DirectBind.div,fold4,f3]
 repeat' first
 | rfl
 | (apply NMT_CallTree.result_congr; intro x; simp only [NMP_PrepareSteps.step,Bind.bind,Pure.pure,NMT_CallTree.erase_bind,NMT_CallTree.erase_invoke,NMT_CallTree.erase_pure,NMT_CallTree.erase_lift,NMT_CallTree.erase,NMT_CallTree.result_assoc,NMT_CallTree.result_right,NMP_DirectBind.ok,NMP_DirectBind.fail,NMP_DirectBind.div,fold4,f3])
 | (split <;> simp only [NMP_PrepareSteps.step,Bind.bind,Pure.pure,NMT_CallTree.erase_bind,NMT_CallTree.erase_invoke,NMT_CallTree.erase_pure,NMT_CallTree.erase_lift,NMT_CallTree.erase,NMT_CallTree.result_assoc,NMT_CallTree.result_right,NMP_DirectBind.ok,NMP_DirectBind.fail,NMP_DirectBind.div,fold4,f3])
#print axioms fold3
end AspisR1.NMP_PrepareSuffix
