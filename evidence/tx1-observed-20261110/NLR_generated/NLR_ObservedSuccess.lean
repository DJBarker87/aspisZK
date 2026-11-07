import NLJ_ObservedDirect
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLR_ObservedSuccess
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code run)
theorem lift_run {A : Type} (raw : Result A) :
 run (show Code A from liftM raw) = ([],raw) := by
 cases raw <;> rfl
#print axioms lift_run
/-- A branch-inversion helper, not a root premise or an independent child
success. Its input is the SAME returning source step in an invocation. -/
theorem bind_return {A B : Type} (code : Code A) (next : A → Code B)
 (out : B) (success : (run (PreparedHashCode.bind code next)).2=ok out) :
 ∃ a, (run code).2=ok a ∧ (run (next a)).2=ok out := by
 rw [AuS1_Trace.run_bind] at success
 cases hc : run code with
 | mk log result =>
  rw [hc] at success
  cases result with
  | fail e => cases success
  | div => cases success
  | ok a => exact ⟨a,rfl,success⟩
#print axioms bind_return
end AspisR1.NLR_ObservedSuccess
end
