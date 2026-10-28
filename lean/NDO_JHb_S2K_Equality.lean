import NDO_JHb_S2K_CopyTransport

/-! Symbolic reflexivity for source array comparisons; no concrete arrays reduced. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S2K.Equality

theorem array_self {T : Type} (cmp : core.cmp.PartialEq T T)
    (same : ∀ x, cmp.ne x x = ok false) {n : Usize} (a : Array T n) :
    core.array.equality.PartialEqArray.eq cmp a a = ok true := by
  have list_self : ∀ xs : List T,
      List.allM (fun (x,y) => do let b ← cmp.ne x y; ok (¬ b))
        (List.zip xs xs) = ok true := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih => simp only [List.zip_cons_cons,List.allM,same,bind_tc_ok]; exact ih
  unfold core.array.equality.PartialEqArray.eq
  rw [if_pos rfl]
  exact list_self a.val

#print axioms array_self
end AspisR1.S2K.Equality
