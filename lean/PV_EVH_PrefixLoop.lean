import PV_EVH_Prefix
set_option autoImplicit false
namespace PV_EVH_PrefixLoop
open Aeneas Aeneas.Std PV_EVH_World PV_EVH_WorldLoop
open PV_EVH_Prefix (P FinishedView)
variable {S A : Type}

/-- Both a nested callee's exhaustion and this loop's exhaustion retain their
post-state and complete emitted prefix. Neither becomes source divergence. -/
def loop (body : S → P (ControlFlow S A)) : Nat → S → P A
  | 0,_,w => ⟨.exhausted,w,[]⟩
  | n+1,s => PV_EVH_Prefix.bind (body s) (fun cf =>
      match cf with
      | .done a => PV_EVH_Prefix.lift (.ok a)
      | .cont next => loop body n next)

theorem fixed_recursive (body : S → P (ControlFlow S A))
    (source : S → Result (ControlFlow S A)) (recur : S → Result A)
    (equation : ∀ s, recur s = Aeneas.Std.bind (source s) (fun cf =>
      match cf with | .done a => .ok a | .cont next => recur next))
    (compatible : ∀ s, FinishedView (body s) (source s))
    (n : Nat) (s : S) : FinishedView (loop body n s) (recur s) := by
  induction n generalizing s with
  | zero => intro w r h; cases h
  | succ n ih =>
    rw [equation s]
    apply PV_EVH_Prefix.bind_fixed
    · exact compatible s
    · intro cf
      cases cf with
      | done a => exact PV_EVH_Prefix.lift_fixed _
      | cont next => exact ih next

theorem nested_exhaustion (body : S → P (ControlFlow S A))
    (n : Nat) (s : S) (w : World)
    (h : (body s w).status = .exhausted) :
    loop body (n+1) s w = ⟨.exhausted,(body s w).world,(body s w).events⟩ := by
  exact PV_EVH_Prefix.bind_exhausted _ _ w h

#print axioms fixed_recursive
#print axioms nested_exhaustion
end PV_EVH_PrefixLoop
