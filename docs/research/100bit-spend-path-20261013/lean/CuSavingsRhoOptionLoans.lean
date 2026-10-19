import AspisR1RhoOptionLeaves.Funs
import AspisR1RhoReferenceDeref.Funs

/-! Exact emitted standard-library leaf behavior. These theorems do not claim
that the producer has translated the nested-borrow `as_deref_mut` caller.
`restore` preserves the original Option discriminant, including on mismatched
handback shapes; it is not an unconstrained identity function. -/
set_option autoImplicit false
namespace AspisR1.CuSavingsRhoOptionLoans
open Aeneas Aeneas.Std Result

def restore {T : Type} (original replacement : Option T) : Option T :=
  match original with
  | none => none
  | some x => some (match replacement with | some y => y | none => x)

theorem as_mut_outcome {T : Type} (original : Option T) :
    AspisR1RhoOptionLeaves.as_mut original = .ok (original,restore original) := by
  cases original with
  | none => rfl
  | some x =>
    simp only [AspisR1RhoOptionLeaves.as_mut,restore]
    congr 2
    funext replacement
    cases replacement <;> rfl

theorem restore_some {T : Type} (x y : T) :
    restore (some x) (some y) = some y := rfl

theorem restore_none {T : Type} (replacement : Option T) :
    restore none replacement = none := rfl

theorem restore_missing {T : Type} (x : T) :
    restore (some x) none = some x := rfl

theorem restore_idempotent {T : Type} (original replacement : Option T) :
    restore original (restore original replacement) = restore original replacement := by
  cases original <;> cases replacement <;> rfl

theorem reborrow_outcome {T : Type} (value : T) :
    AspisR1RhoReferenceDeref.reborrow value =
      .ok (value,id,id) := rfl

/-- The exact source identity returns two identity handbacks. Projecting one
is valid only after this equation; no mutable-reference primitive is assumed. -/
theorem reborrow_project {T : Type} (value : T) :
    (do let (v,outer,inner) ← AspisR1RhoReferenceDeref.reborrow value
        pure (v,fun replacement => outer (inner replacement))) =
      (.ok (value,id) : Result (T × (T → T))) := rfl

/-- Exact `map` retains callback failure and divergence in the Some branch. -/
theorem map_some {T U F : Type}
    (inst : core.ops.function.FnOnce F T U) (f : F) (x : T) :
    AspisR1RhoOptionLeaves.map inst (some x) f =
      (do let y ← inst.call_once f x; pure (some y)) := rfl

theorem map_none {T U F : Type}
    (inst : core.ops.function.FnOnce F T U) (f : F) :
    AspisR1RhoOptionLeaves.map inst none f = .ok none := rfl

/-- An explicitly packaged source reborrow keeps both emitted writebacks. -/
structure Loan (T : Type) where
  value : T
  outer : T → T
  inner : T → T

def reborrowFn (T : Type) : core.ops.function.FnOnce Unit T (Loan T) :=
  {call_once := fun _ value => do
    let (v,outer,inner) ← AspisR1RhoReferenceDeref.reborrow value
    pure ⟨v,outer,inner⟩}

/-- Compose the emitted generic leaves while retaining loan handbacks as
values. Binding this packaging to the original nested-borrow caller is a
separate source-lowering obligation. -/
def packaged {T : Type} (original : Option T) :
    Result (Option (Loan T) × (Option T → Option T)) := do
  let (o,back) ← AspisR1RhoOptionLeaves.as_mut original
  let loans ← AspisR1RhoOptionLeaves.map (reborrowFn T) o ()
  pure (loans,back)

theorem packaged_some {T : Type} (x : T) :
    packaged (some x) = .ok (some ⟨x,id,id⟩,restore (some x)) := by
  unfold packaged
  rw [as_mut_outcome]
  rfl

theorem packaged_none {T : Type} :
    packaged (none : Option T) = .ok (none,restore none) := rfl

theorem packaged_write {T : Type} (x replacement : T) :
    (do let (loans,back) ← packaged (some x)
        match loans with
        | none => .fail .panic
        | some loan => pure (back (some (loan.outer (loan.inner replacement))))) =
      (.ok (some replacement) : Result (Option T)) := rfl

#print axioms as_mut_outcome
#print axioms restore_idempotent
#print axioms reborrow_project
#print axioms map_some
#print axioms map_none
#print axioms packaged_some
#print axioms packaged_none
#print axioms packaged_write
end AspisR1.CuSavingsRhoOptionLoans
