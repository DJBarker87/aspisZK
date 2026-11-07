import NMP_CutAlgebra
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_ReachedAlgebra
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Code run Log)
/-- Only the actual returned argument needs a continuation law. This avoids
requiring a callee certificate outside the domains any caller establishes. -/
theorem bind {α β : Type} (x y : Code α) (k l : α → Code β)
 (head : run x = run y)
 (tail : ∀ log a, run x=(log,ok a) → run (k a)=run (l a)) :
 run (PreparedHashCode.bind x k)=run (PreparedHashCode.bind y l) := by
 rw [NMP_CutAlgebra.run_bind,NMP_CutAlgebra.run_bind,head]
 cases h : run y with
 | mk log reply =>
  cases reply with
  | ok a =>
   have actual := head.trans h
   simp only [NMP_CutAlgebra.bind,tail log a actual]
  | fail e => rfl
  | div => rfl
#print axioms bind
end AspisR1.NMP_ReachedAlgebra
end
