import Mathlib.Data.Fintype.Fin
set_option autoImplicit false
namespace PV_L2C_FirstInactive
/-- Literal first_inactive_row scan: None records the public all-active panic
case, rather than silently installing a successful selector. -/
def first : List Bool → Option Nat
 | [] => none
 | false::_ => some 0
 | true::xs => (first xs).map Nat.succ

theorem returned (xs : List Bool) (i : Nat) (h : first xs=some i) :
    i<xs.length ∧ xs[i]?=some false := by
  induction xs generalizing i with
  | nil => simp [first] at h
  | cons b bs ih =>
    cases b with
    | false =>
      simp only [first,Option.some.injEq] at h
      subst i
      exact ⟨by simp, rfl⟩
    | true =>
      cases ht : first bs with
      | none => simp [first,ht] at h
      | some j =>
        simp only [first,ht,Option.map_some,Option.some.injEq] at h
        subst i
        obtain ⟨hb,hv⟩ := ih j ht
        exact ⟨by simpa using Nat.succ_lt_succ hb,by simpa using hv⟩
#print axioms returned

theorem table_returned {n : Nat} (active : Fin n → Bool) (d : Nat)
    (h : first (List.ofFn active)=some d) : ∃ hd : d<n, active ⟨d,hd⟩=false := by
  obtain ⟨hb,hv⟩ := returned (List.ofFn active) d h
  have hd : d<n := by simpa using hb
  refine ⟨hd,?_⟩
  have he : (List.ofFn active)[d]?=some (active ⟨d,hd⟩) := by simp [hd]
  rw [he] at hv
  exact Option.some.inj hv
#print axioms table_returned
end PV_L2C_FirstInactive
