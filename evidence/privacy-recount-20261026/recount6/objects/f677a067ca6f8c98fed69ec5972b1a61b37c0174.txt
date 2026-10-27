import R1Z.PV_Join_Canonical5
set_option autoImplicit false
namespace R1Z.PV_Join_CanonicalArray5
open Aeneas Aeneas.Std ProverRwFull PV_Join_Canonical5

theorem list_repeat (q : aspis_core.field.QM31) (hq : Q q) (n : Nat) :
    ∀ x ∈ List.replicate n q, Q x := by
  intro x hx
  simpa only [List.eq_of_mem_replicate hx] using hq

theorem array_repeat {n : Usize} (q : aspis_core.field.QM31) (hq : Q q) :
    QArray (Array.repeat n q) := by
  exact list_repeat q hq n.val

theorem list_set (xs : List aspis_core.field.QM31)
    (hxs : ∀ x ∈ xs, Q x) (i : Nat) (q : aspis_core.field.QM31) (hq : Q q) :
    ∀ x ∈ xs.set i q, Q x := by
  induction xs generalizing i with
  | nil => intro x hx; simp only [List.set_nil, List.not_mem_nil] at hx
  | cons a xs ih =>
    cases i with
    | zero =>
      intro x hx
      simp only [List.set_cons_zero, List.mem_cons] at hx
      rcases hx with hx | hx
      · subst x; exact hq
      · exact hxs x (List.mem_cons_of_mem a hx)
    | succ i =>
      intro x hx
      simp only [List.set_cons_succ, List.mem_cons] at hx
      rcases hx with hx | hx
      · subst x; exact hxs a (by simp)
      · exact ih (by intro y hy; exact hxs y (List.mem_cons_of_mem a hy)) i x hx


#print axioms list_repeat
#print axioms array_repeat
#print axioms list_set
end R1Z.PV_Join_CanonicalArray5
