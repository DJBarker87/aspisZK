import NLI_Monad
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLI_RunLaws
open Aeneas Aeneas.Std AspisR1PublicPreparation
open PreparedHashCode (Code run)
theorem bind_congr {A B : Type} (p : Code A) (k l : A → Code B)
 (eqs : ∀ a, run (k a) = run (l a)) :
 run (PreparedHashCode.bind p k) = run (PreparedHashCode.bind p l) := by
 rw [AuS1_Trace.run_bind, AuS1_Trace.run_bind]
 cases h : run p with
 | mk log reply =>
  cases reply with
  | ok a => simp only [AuS1_Trace.continueRun,eqs a]
  | fail e => rfl
  | div => rfl
theorem step_ok {A B : Type} (a : A) (k : A → Code B) :
 run (.step (.ok a) k) = run (k a) := rfl
#print axioms bind_congr
#print axioms step_ok
end AspisR1.NLI_RunLaws
end
