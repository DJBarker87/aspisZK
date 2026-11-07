import NMP_ObservedNormal
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_ObservedSuffix
open Aeneas Aeneas.Std Result NMP_prepare NMP_Emitted
open NMP_ObservedSteps (State execute body)
open NMT_CallTree (erase)
/-- One source occurrence and the already-compiled suffix; all Result arms. -/
theorem fold5 {H W : Type} (c : Calls) (s : Parent H W) (p : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H) (ch : aspis_core.state_only_prefix.r0.Challenges) :
 erase (execute c 1 (.finish s p t ch)) = f5 c s p t ch := by
 rw [execute]
 simp only [NMP_ObservedSteps.step,Bind.bind,Pure.pure,NMT_CallTree.erase_bind,NMT_CallTree.erase_invoke,NMT_CallTree.erase_pure,NMT_CallTree.erase,NMT_CallTree.result_assoc,NMT_CallTree.result_right,bind_tc_ok,f5]
 repeat' first
 | rfl
 | (apply NMT_CallTree.result_congr; intro x; simp only [NMP_ObservedSteps.step,Bind.bind,Pure.pure,NMT_CallTree.erase_bind,NMT_CallTree.erase_invoke,NMT_CallTree.erase_pure,NMT_CallTree.erase,NMT_CallTree.result_assoc,NMT_CallTree.result_right,bind_tc_ok,f5])
 | (split <;> simp only [NMP_ObservedSteps.step,Bind.bind,Pure.pure,NMT_CallTree.erase_bind,NMT_CallTree.erase_invoke,NMT_CallTree.erase_pure,NMT_CallTree.erase,NMT_CallTree.result_assoc,NMT_CallTree.result_right,bind_tc_ok,f5])
#print axioms fold5
end AspisR1.NMP_ObservedSuffix
