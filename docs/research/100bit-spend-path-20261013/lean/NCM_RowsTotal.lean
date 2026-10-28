import NCM_RowProgress

set_option autoImplicit false
namespace AspisR1.NCM_RowsTotal
open Aeneas Aeneas.Std Result MultiproofConeRef
open MultiproofConeNodeDomain MultiproofConeNodeIteration

/-- Sufficient fuel is derived from the actual remaining input nodes. It
excludes administrative divergence without assuming an accepted level. -/
theorem total {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (hashTotal : HashTotal D hash) (physical : Slice U8) (fuel : Nat)
    (s : reference.Scratch) (i w : Usize) (domain : RowDomain physical s i w)
    (bound : s.n.val-i.val ≤ fuel) :
    ∃ out, rows (fun s i w => reference.binary_step D hash s physical i w) fuel s i w = ok out := by
  induction fuel generalizing s i w with
  | zero =>
    have halt : i≥s.n := by scalar_tac
    exact ⟨.Done {s with n:=w},by simp only [rows,halt,if_true]⟩
  | succ fuel ih =>
    by_cases halt : i≥s.n
    · exact ⟨.Done {s with n:=w},by simp only [rows,halt,if_true]⟩
    · obtain ⟨out,returned,post⟩ := binary_step_progress D hash hashTotal physical s i w domain (by scalar_tac)
      simp only [rows,halt,if_false,returned,bind_tc_ok]
      cases out with
      | Stop stopped => exact ⟨.Stop stopped,rfl⟩
      | Next after ni nw =>
        exact ih after ni nw post.2.1 (by rw [post.1]; have := post.2.2.1; omega)

#print axioms total
end AspisR1.NCM_RowsTotal
