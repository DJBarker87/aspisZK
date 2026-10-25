import Hist_DistinctBody
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hist_DistinctInner
open Aeneas Aeneas.Std Result ControlFlow
open Hist_DistinctBody
abbrev Key := AdapterRw.solana_pubkey.Pubkey
local instance : DecidableEq Key := Classical.decEq _

def keyAt {N : Usize} (accounts : Array Account N) (i : Fin N.val) : Key :=
  (accounts.val[i.val]'(by rw [accounts.property]; exact i.isLt)).key

def Post {N : Usize} (accounts : Array Account N) (index : Fin N.val) (start : Nat) :
    Option (core.result.Result Unit PE) → Prop
  | none => ∀ j : Fin N.val, start ≤ j.val → j.val < index.val → keyAt accounts j ≠ keyAt accounts index
  | some (.Err _) => True
  | some (.Ok _) => False

/-- Exact extracted inner alias-check loop: total on its admitted bounds,
and None proves every prior comparison differs. No concrete array unrolling. -/
theorem inner_spec {N : Usize} (base : AdapterRw.Ops) (accounts : Array Account N)
    (index previous : Usize) (bound : index < N) (ordered : previous.val ≤ index.val) :
    AdapterRw.r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0
      (Hist_Authority.install base) accounts index previous
      ⦃ Post accounts ⟨index.val,by scalar_tac⟩ previous.val ⦄ := by
  unfold AdapterRw.r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0
  apply loop.spec_decr_nat (fun p : Usize => index.val-p.val)
    (fun p => p.val ≤ index.val ∧ ∀ j : Fin N.val, previous.val ≤ j.val →
      j.val < p.val → keyAt accounts j ≠ keyAt accounts ⟨index.val,by scalar_tac⟩)
    (Post accounts ⟨index.val,by scalar_tac⟩ previous.val)
  · intro p inv
    by_cases running : p < index
    · rw [Hist_DistinctBody.body base accounts index p bound running]
      split
      · change True
        trivial
      · rename_i unequal
        rw [WP.spec_ok]
        dsimp only
        have next := Hist_DistinctBody.successor p index running
        constructor
        · constructor
          · rw [next]; scalar_tac
          · intro j start lt
            by_cases old : j.val < p.val
            · exact inv.2 j start old
            · have same : j.val = p.val := by rw [next] at lt; omega
              simpa only [keyAt,same] using unequal
        · rw [next]
          scalar_tac
    · rw [AdapterRw.r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0.body,if_neg running]
      rw [WP.spec_ok]
      change ∀ j : Fin N.val, previous.val ≤ j.val → j.val < index.val → _
      intro j start lt
      exact inv.2 j start (by scalar_tac)
  · exact ⟨ordered,by intro j start lt; omega⟩

#print axioms inner_spec
end AspisR1.Hist_DistinctInner
end
