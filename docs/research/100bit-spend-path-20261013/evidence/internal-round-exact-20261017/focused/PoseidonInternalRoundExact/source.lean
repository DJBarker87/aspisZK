import PoseidonInternalLinearExact

/-! Exact missing internal_round declaration from candidate Funs SHA
f1e258056294e84777f56f2a1ea3572329eca52b4bb553bfc6c58027bef1604c,
source state_only_poseidon.rs lines 387--391, followed by its refinement.
Existing add, pow5, update and internal-linear proofs are reused. -/
set_option autoImplicit false
namespace AspisR1SelectedMaskProbe
open Aeneas Aeneas.Std Result

def state_only_poseidon.internal_round
  (state : Array field.QM31 16#usize) (constant1 : field.QM31) :
  Result (Array field.QM31 16#usize)
  := do
  let q ← Array.index_usize state 0#usize
  let q1 ← field.QM31.add q constant1
  let q2 ← state_only_poseidon.pow5 q1
  let state1 ← Array.update state 0#usize q2
  state_only_poseidon.internal_linear_lazy state1
end AspisR1SelectedMaskProbe

namespace AspisR1.PoseidonInternalRoundExact
open Aeneas Aeneas.Std Result WP
open AspisR1SelectedMaskProbe
open AspisR1.PoseidonFullRoundCellStep

theorem source_success (state : State) (constant1 : QM)
    (hstate : CanonicalState state) (hc : Canonical constant1) :
    ∃ out : State, state_only_poseidon.internal_round state constant1 = .ok out ∧
      CanonicalState out ∧ ∀ j : Fin 16, Decode (cell out j) =
        R0P.poseidonInternalRound (fun i : Fin 16 => Decode (cell state i)) (Decode constant1) j := by
  let old := cell state (0 : Fin 16)
  have hread : Array.index_usize state 0#usize = .ok old :=
    AspisR1.PoseidonInternalStateWords.state_source_read state 0#usize (by decide)
  obtain ⟨added,hadd,haddedCan,haddedModel⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact old constant1 (hstate 0) hc
  obtain ⟨value,hpow,hcan,hmodel⟩ := AspisR1.PoseidonPow5SourceExact.source_success added haddedCan
  change Decode added = Decode old + Decode constant1 at haddedModel
  change Decode value = R0P.poseidonPow5 (Decode added) at hmodel
  have hvalue : Decode value = R0P.poseidonPow5 (Decode old + Decode constant1) :=
    hmodel.trans (congrArg R0P.poseidonPow5 haddedModel)
  let state1 := state.set 0#usize value
  have hupdate : Array.update state 0#usize value = .ok state1 := by
    obtain ⟨out,hrun,hset⟩ := WP.spec_imp_exists (Array.update_spec state 0#usize value (by simp))
    simpa only [hset] using hrun
  obtain ⟨out,hrun,houtCan,houtModel⟩ := AspisR1.PoseidonInternalLinearExact.source_success
    state1 (set_canonical state 0#usize value hstate hcan)
  have hdecoded : (fun j : Fin 16 => Decode (cell state1 j)) =
      (fun j : Fin 16 => if j = 0 then R0P.poseidonPow5
        (Decode (cell state (0 : Fin 16)) + Decode constant1) else Decode (cell state j)) := by
    funext j
    change Decode (cell (state.set 0#usize value) j) = _
    rw [cell_set]
    have h0 : (0#usize).val = 0 := by decide
    rw [h0]
    by_cases hz : j.val = 0
    · have hfin : j = (0 : Fin 16) := Fin.ext hz
      rw [if_pos hz,if_pos hfin]
      change Decode value = R0P.poseidonPow5 (Decode old + Decode constant1)
      exact hvalue
    · have hfin : j ≠ (0 : Fin 16) := fun h => hz (congrArg Fin.val h)
      rw [if_neg hz,if_neg hfin]
  refine ⟨out,?_,houtCan,?_⟩
  · simp only [state_only_poseidon.internal_round,hread,hadd,hpow,hupdate,bind_tc_ok]
    exact hrun
  · intro j
    change Decode (cell out j) = R0P.poseidonInternalLinear
      (fun i : Fin 16 => if i = 0 then R0P.poseidonPow5
        (Decode (cell state (0 : Fin 16)) + Decode constant1) else Decode (cell state i)) j
    exact (houtModel j).trans
      (congrArg (fun f : Fin 16 → Exact => R0P.poseidonInternalLinear f j) hdecoded)

#print axioms source_success
end AspisR1.PoseidonInternalRoundExact
