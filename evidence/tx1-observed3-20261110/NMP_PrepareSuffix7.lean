import NMP_PrepareNormal
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_PrepareSuffix
open Aeneas Aeneas.Std Result NMP_prepare NMP_Emitted NMP_PrepareSteps
open NMT_CallTree (erase)
/-- One source call and the already-compiled suffix; no whole-state unfolding. -/
theorem fold7 {H W : Type} (c : Calls) (s : Parent H W) (v : verifier.View) (sem : r1_semantic.Verified H) :
 erase (execute c 1 (.prepared s v sem)) = f7 c s v sem := by
 rw [execute]
 simp only [NMP_PrepareSteps.step,Bind.bind,Pure.pure,NMT_CallTree.erase_bind,NMT_CallTree.erase_invoke,NMT_CallTree.erase_pure,NMT_CallTree.erase_lift,NMT_CallTree.erase,NMT_CallTree.result_assoc,NMT_CallTree.result_right,NMP_DirectBind.ok,NMP_DirectBind.fail,NMP_DirectBind.div,f7]
 repeat' first
 | rfl
 | (apply NMT_CallTree.result_congr; intro x; simp only [NMP_PrepareSteps.step,Bind.bind,Pure.pure,NMT_CallTree.erase_bind,NMT_CallTree.erase_invoke,NMT_CallTree.erase_pure,NMT_CallTree.erase_lift,NMT_CallTree.erase,NMT_CallTree.result_assoc,NMT_CallTree.result_right,NMP_DirectBind.ok,NMP_DirectBind.fail,NMP_DirectBind.div,f7])
 | (split <;> simp only [NMP_PrepareSteps.step,Bind.bind,Pure.pure,NMT_CallTree.erase_bind,NMT_CallTree.erase_invoke,NMT_CallTree.erase_pure,NMT_CallTree.erase_lift,NMT_CallTree.erase,NMT_CallTree.result_assoc,NMT_CallTree.result_right,NMP_DirectBind.ok,NMP_DirectBind.fail,NMP_DirectBind.div,f7])
#print axioms fold7
end AspisR1.NMP_PrepareSuffix
