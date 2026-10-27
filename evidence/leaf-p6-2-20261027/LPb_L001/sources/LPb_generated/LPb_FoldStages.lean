import XRk_DotModel
open Aeneas Aeneas.Std Result
namespace LPb_FoldStages
/-- The fold preserves the actual Result, including panic and divergence. -/
theorem congr {α β : Type} (xs : List α) (initial : β)
    (f g : β → α → Result β) (steps : ∀ state item, f state item = g state item) :
    xs.foldlM f initial = xs.foldlM g initial := by
  have same : f = g := funext (fun s => funext (steps s))
  rw [same]

def powerStep (x p : XRk_Wide) : Result XRk_Wide :=
  XRk_Release.aspis_core.field.wide_exact.WideExact.mul p x

theorem powers_zero (x p : XRk_Wide) : XRk_powers x 0 p = ok [] := rfl
theorem powers_one (x p : XRk_Wide) : XRk_powers x 1 p = ok [p] := rfl
theorem powers_next (x p : XRk_Wide) (n : Nat) :
    XRk_powers x (n+2) p = (do
      let next ← powerStep x p
      let rest ← XRk_powers x (n+1) next
      ok (p::rest)) := rfl

/-- Does not assume any multiplication is commutative. -/
theorem powers_seven (x p : XRk_Wide) :
    XRk_powers x 7 p = (do
      let next ← powerStep x p
      let rest ← XRk_powers x 6 next
      ok (p::rest)) := rfl
#print axioms congr
#print axioms powers_zero
#print axioms powers_one
#print axioms powers_next
#print axioms powers_seven
end LPb_FoldStages
