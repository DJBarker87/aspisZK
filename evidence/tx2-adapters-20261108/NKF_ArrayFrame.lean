import NKF_BoxModel
set_option autoImplicit false
noncomputable section
namespace NKF_ArrayFrame
open Aeneas Aeneas.Std Result
def CellEq {A : Type} {n : Usize} (before after : Array A n) : Prop :=
 ∀ i : Nat, before.val[i]? = after.val[i]?

theorem array_ext {A : Type} {n : Usize} (before after : Array A n)
 (cells : CellEq before after) : before = after := by
 have lists : before.val = after.val := by
  apply List.ext_getElem?
  exact cells
 cases before
 cases after
 cases lists
 rfl
#print axioms array_ext

/-- Value-level arbitrary-window frame, used only after the matching native
one-window cut is established; no native pass follows from this theorem. -/
theorem point_frame {A : Type} (before after : Nat → A) (offset : Nat)
 (value : A) (written : after offset = value)
 (frame : ∀ i, i ≠ offset → after i = before i) :
 after = fun i => if i = offset then value else before i := by
 funext i
 by_cases same : i=offset
 · subst i; simp only [ite_true,written]
 · simp only [same,ite_false]; exact frame i same
#print axioms point_frame
end NKF_ArrayFrame
