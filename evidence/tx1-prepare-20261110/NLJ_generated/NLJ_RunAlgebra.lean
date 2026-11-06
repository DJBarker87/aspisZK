import NLJ_CodeRight
import RPz7_AuS1_Trace
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_RunAlgebra
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code run)
theorem bind_congr {A B : Type} (c : Code A) (f g : A → Code B)
 (h : ∀ a, run (f a) = run (g a)) :
 run (PreparedHashCode.bind c f) = run (PreparedHashCode.bind c g) := by
 rw [AuS1_Trace.run_bind,AuS1_Trace.run_bind]
 cases hc : run c with
 | mk log out =>
   cases out with
   | ok a => simp only [AuS1_Trace.continueRun,h a]
   | fail e => rfl
   | div => rfl
/-- Silent pure administrative steps are observable only through their value.
This is a run law, not an incorrect claim that the Code trees are identical. -/
theorem inl_return {A B : Type} (c : Code A) (k : Sum A B → Code A)
 (returned : ∀ a, run (k (.inl a)) = ([],ok a)) :
 run (PreparedHashCode.bind (PreparedHashCode.bind c (fun a => .done (.inl a))) k) = run c := by
 rw [NLJ_Monad.bind_assoc]
 rw [AuS1_Trace.run_bind]
 cases hc : run c with
 | mk log out =>
   cases out with
   | ok a => simp only [AuS1_Trace.continueRun,NLJ_Monad.bind_pure,returned,List.append_nil]
   | fail e => rfl
   | div => rfl
#print axioms bind_congr
#print axioms inl_return
end AspisR1.NLJ_RunAlgebra
end
