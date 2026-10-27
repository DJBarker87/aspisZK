import R1Z.ProverCommitBinaryGroup46
/-! Finite cursor-erased owner for the native per-parent transition. Every
consumed input is dropped once; sufficient fuel is bounded by input length.
This does not replace the native array/cursor representation certificate. -/
set_option autoImplicit false
namespace R1Z.ProverCommitBinaryCursor46
open Aeneas Aeneas.Std Result ProverCommitBinaryGroup46

def source : Nat → List U32 → Result (List U32 × List U32)
  | 0,[] => ok ([],[])
  | 0,_::_ => .div
  | _+1,[] => ok ([],[])
  | fuel+1,a::tail => do
    let g ← AspisR1BinaryGroup46.reference a tail.head?
    let rest ← source fuel ((a::tail).drop g.consumed.val)
    ok (g.parent::rest.1,g.sibling.toList ++ rest.2)

theorem drop_group (a : U32) (tail : List U32) :
    (a::tail).drop (group a tail.head?).consumed.val =
      tail.drop ((group a tail.head?).consumed.val-1) := by
  unfold group
  split <;> rfl

/-- Kernel-checked induction over native per-group reference calls. No large
numerals are evaluated, and no whole multiproof success law is assumed. -/
theorem source_layer (fuel : Nat) (xs : List U32) (bound : xs.length≤fuel) :
    source fuel xs = ok (layer xs) := by
  induction fuel generalizing xs with
  | zero =>
    have hx : xs=[] := List.length_eq_zero_iff.mp (by omega)
    subst xs
    simp only [source,layer]
  | succ fuel ih =>
    cases xs with
    | nil => simp only [source,layer]
    | cons a tail =>
      rw [source,group_exact]
      simp only [bind_tc_ok,drop_group]
      rw [ih _ (by simp only [List.length_drop,List.length_cons] at *;omega)]
      simp only [bind_tc_ok,layer]

theorem native_layer (xs : List U32) : source xs.length xs = ok (layer xs) :=
  source_layer xs.length xs (Nat.le_refl _)

#print axioms drop_group
#print axioms source_layer
#print axioms native_layer
end R1Z.ProverCommitBinaryCursor46
