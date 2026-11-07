import NMP_ObservedSuffix2
import NMP_DirectBind
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_ObservedSuffix
open Aeneas Aeneas.Std Result NMP_prepare NMP_Emitted
open NMP_ObservedSteps (State execute body)
open NMT_CallTree (erase)
/-- One source occurrence and the already-compiled suffix; all Result arms. -/
theorem fold1 {H W : Type} (c : Calls) (s : Parent H W) (p : r1_wire.Prefix) :
 erase (execute c 5 (.mark0 s p)) = f1 c s p := by
 rw [execute]
 simp only [NMP_ObservedSteps.step,Bind.bind,Pure.pure,NMT_CallTree.erase_bind,NMT_CallTree.erase_invoke,NMT_CallTree.erase_pure,NMT_CallTree.erase,NMT_CallTree.result_assoc,NMT_CallTree.result_right,NMP_DirectBind.ok,NMP_DirectBind.fail,NMP_DirectBind.div,fold2,f1]
 repeat' first
 | rfl
 | (apply NMT_CallTree.result_congr; intro x; simp only [NMP_ObservedSteps.step,Bind.bind,Pure.pure,NMT_CallTree.erase_bind,NMT_CallTree.erase_invoke,NMT_CallTree.erase_pure,NMT_CallTree.erase,NMT_CallTree.result_assoc,NMT_CallTree.result_right,NMP_DirectBind.ok,NMP_DirectBind.fail,NMP_DirectBind.div,fold2,f1])
 | (split <;> simp only [NMP_ObservedSteps.step,Bind.bind,Pure.pure,NMT_CallTree.erase_bind,NMT_CallTree.erase_invoke,NMT_CallTree.erase_pure,NMT_CallTree.erase,NMT_CallTree.result_assoc,NMT_CallTree.result_right,NMP_DirectBind.ok,NMP_DirectBind.fail,NMP_DirectBind.div,fold2,f1])
#print axioms fold1
end AspisR1.NMP_ObservedSuffix
