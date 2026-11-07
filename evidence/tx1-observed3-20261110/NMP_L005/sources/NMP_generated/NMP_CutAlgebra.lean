import NLJ_RunAlgebra
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_CutAlgebra
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code run Log)
abbrev Outcome (α : Type) := Log × Result α
/-- A stopped child has its attempted-event prefix, and no continuation heap. -/
def bind {α β : Type} (x : Outcome α) (k : α → Outcome β) : Outcome β :=
 match x.2 with
 | .ok a => (x.1 ++ (k a).1,(k a).2)
 | .fail e => (x.1,.fail e)
 | .div => (x.1,.div)
theorem run_bind {α β : Type} (x : Code α) (k : α → Code β) :
 run (PreparedHashCode.bind x k) = bind (run x) (fun a => run (k a)) := by
 rw [AuS1_Trace.run_bind]
 cases h : run x with
 | mk log reply => cases reply <;> rfl
/-- Used only at the SAME recorded arguments; it is not a native producer. -/
theorem congr_run {α β : Type} (x y : Code α) (k l : α → Code β)
 (head : run x = run y) (tail : ∀ a, run (k a) = run (l a)) :
 run (PreparedHashCode.bind x k) = run (PreparedHashCode.bind y l) := by
 rw [run_bind,run_bind,head]
 cases h : run y with
 | mk log reply =>
  cases reply with
  | ok a => simp only [bind,tail a]
  | fail e => rfl
  | div => rfl
theorem fail_prefix {α β : Type} (log : Log) (e : Error) (k : α → Outcome β) :
 bind (log,.fail e) k = (log,.fail e) := rfl
theorem div_prefix {α β : Type} (log : Log) (k : α → Outcome β) :
 bind (log,.div) k = (log,.div) := rfl
#print axioms run_bind
#print axioms congr_run
#print axioms fail_prefix
#print axioms div_prefix
end AspisR1.NMP_CutAlgebra
end
