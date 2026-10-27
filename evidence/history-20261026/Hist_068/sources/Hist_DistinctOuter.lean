import Hist_DistinctInner
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hist_DistinctOuter
open Aeneas Aeneas.Std Result ControlFlow Hist_DistinctBody
open Hist_DistinctInner (keyAt)

def Post {N : Usize} (accounts : Array Account N) (start : Nat) :
    Option (core.result.Result Unit PE) → Prop
  | none => ∀ i j : Fin N.val, start ≤ i.val → j.val < i.val → keyAt accounts j ≠ keyAt accounts i
  | some (.Err _) => True
  | some (.Ok _) => False

theorem outer_spec {N : Usize} (base : AdapterRw.Ops) (accounts : Array Account N)
    (index : Usize) (bound : index.val ≤ N.val) :
    AdapterRw.r1_pool_adapter.owned.require_distinct_accounts_loop0
      (Hist_Authority.install base) accounts index ⦃ Post accounts index.val ⦄ := by
  unfold AdapterRw.r1_pool_adapter.owned.require_distinct_accounts_loop0
  apply loop.spec_decr_nat (fun p : Usize => N.val-p.val)
    (fun p => p.val ≤ N.val ∧ ∀ i j : Fin N.val, index.val ≤ i.val →
      i.val < p.val → j.val < i.val → keyAt accounts j ≠ keyAt accounts i)
    (Post accounts index.val)
  · intro p inv
    by_cases running : p < N
    · obtain ⟨result,run,post⟩ := WP.spec_imp_exists
        (Hist_DistinctInner.inner_spec base accounts p 0#usize running (by scalar_tac))
      rw [AdapterRw.r1_pool_adapter.owned.require_distinct_accounts_loop0.body,if_pos running,run,bind_tc_ok]
      cases result with
      | none =>
        simp only [lift,bind_tc_ok]
        rw [WP.spec_ok]
        dsimp only
        have next := Hist_DistinctBody.successor p N running
        constructor
        · constructor
          · rw [next]; scalar_tac
          · intro i j start lt jl
            by_cases old : i.val < p.val
            · exact inv.2 i j start old jl
            · have same : i.val = p.val := by rw [next] at lt; omega
              have pair := post j (Nat.zero_le _) (by simpa only [same] using jl)
              simpa only [keyAt,same] using pair
        · rw [next]; scalar_tac
      | some inner =>
        cases inner with
        | Err error => change True; trivial
        | Ok unit => exact False.elim post
    · rw [AdapterRw.r1_pool_adapter.owned.require_distinct_accounts_loop0.body,if_neg running]
      rw [WP.spec_ok]
      intro i j start jl
      exact inv.2 i j start (by scalar_tac) jl
  · exact ⟨bound,by intro i j start lt jl; omega⟩

/-- The program's actual complete distinct-account guard, not an assumed
pairwise-key predicate, excludes every equal prior key. -/
theorem accepted {N : Usize} (base : AdapterRw.Ops) (accounts : Array Account N)
    (success : AdapterRw.r1_pool_adapter.owned.require_distinct_accounts
      (Hist_Authority.install base) accounts = ok (.Ok ())) :
    ∀ i j : Fin N.val, j.val < i.val → keyAt accounts j ≠ keyAt accounts i := by
  obtain ⟨result,run,post⟩ := WP.spec_imp_exists (outer_spec base accounts 0#usize (by scalar_tac))
  unfold AdapterRw.r1_pool_adapter.owned.require_distinct_accounts at success
  rw [run,bind_tc_ok] at success
  cases result with
  | none => intro i j jl; exact post i j (Nat.zero_le _) jl
  | some inner => cases inner with
    | Err error => cases success
    | Ok unit => exact False.elim post

#print axioms outer_spec
#print axioms accepted
end AspisR1.Hist_DistinctOuter
end
