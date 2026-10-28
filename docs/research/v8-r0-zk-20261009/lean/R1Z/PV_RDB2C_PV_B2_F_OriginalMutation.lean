import R1Z.PV_RDB2C_PV_B2_F_MutationModel
import R1Z.PV_RDB2C_PV_B2_F_ArrayMutation
import R1Z.PV_RDB2C_PV_B2_F_CellAccumulate
set_option autoImplicit false
namespace PV_B2_F_OriginalMutation
open Aeneas Aeneas.Std Result PV_B2_251c1 PV_B2_C_MutationStep PV_B2_F_ArrayMutation
/-- Complete ordered outer iterator, with the current value read before the
original inner accumulator. The update restores the consumed mutable slot. -/
def remaining (w : host_weights.Weights) (k : Powers) : Nat → Usize → Out → Result Out
  | 0, _, out => ok out
  | n+1, j, out => do
    let initial ← Array.index_usize out j
    let x ← PV_B2_F_CellAccumulate.original w k j initial
    let out1 ← Array.update out j x
    remaining w k n (Usize.wrapping_add j 1#usize) out1

/-- Source loop equality on exactly the zero-filled allocation invariant.
Every intermediate write is retained; no whole-loop kernel evaluation. -/
theorem loop (w : host_weights.Weights) (k : Powers) (out : Out) (j : Usize)
    (hz : ZeroSuffix out j.val) :
    remaining w k (1024-j.val) j out =
      PV_B2_F_MutationModel.remaining w k (1024-j.val) j out := by
  suffices ∀ n (j : Usize) (out : Out), 1024-j.val=n → ZeroSuffix out j.val →
    remaining w k n j out = PV_B2_F_MutationModel.remaining w k n j out from
    this (1024-j.val) j out rfl hz
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro j out hn hz
    have hj : j < 1024#usize := by scalar_tac
    have hj' : j.val < out.val.length := by rw [out.property]; exact hj
    obtain ⟨initial,hi,hiv⟩ := WP.spec_imp_exists (Array.index_usize_spec out j hj')
    have hzero : initial = aspis_core.field.wide_exact.WideExact.ZERO := by
      have hslot := hz j.val (by omega) hj
      -- Convert the checked read's slot equation to the suffix's Option view.
      have hread : out.val[j.val]? = some initial := by
        unfold Array.index_usize at hi
        split at hi
        · cases hi
        · rename_i v hv
          cases Result.ok.inj hi
          exact hv
      exact Option.some.inj (hread.symm.trans hslot)
    rw [hzero] at hi
    simp only [remaining,PV_B2_F_MutationModel.remaining,hi,bind_tc_ok,
      PV_B2_F_CellAccumulate.zero]
    obtain ⟨x,hx⟩ := PV_B2_D_MaterializeTotal.cell w k j hj
    rw [PV_B2_F_CellFold.source] at hx
    simp only [hx,bind_tc_ok]
    obtain ⟨out1,hu⟩ := PV_B2_C_MutationLoop.update_total out j x hj
    simp only [hu,bind_tc_ok]
    have hv := PV_B2_C_MutationTotal.next_val j hj
    exact ih _ _ (by rw [hv]; omega) (by
      rw [hv]
      exact suffix_step out out1 j x hz hu)
#print axioms loop
end PV_B2_F_OriginalMutation
