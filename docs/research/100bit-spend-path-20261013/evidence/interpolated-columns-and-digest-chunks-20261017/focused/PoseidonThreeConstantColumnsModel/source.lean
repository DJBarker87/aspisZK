import PoseidonThreeConstantColumnStep
import AspisR1.ArrayZeroExact

/-! The actual while loop constructs all sixteen interpolated constants.
The invariant is a prefix of exact modeled cells and an unchanged suffix. -/
set_option autoImplicit false
namespace AspisR1.PoseidonThreeConstantColumnsModel
open Aeneas Aeneas.Std Result WP
open AspisR1SelectedMaskProbe
open AspisR1.PoseidonFullRoundCellStep
open AspisR1.PoseidonThreeConstantColumnStep

theorem loop_success_fuel (weights : Weights) (c0 c1 c2 : Constants) (out : State)
    (lane : Usize) (fuel : Nat) (hspan : lane.val + fuel = 16)
    (hw : CanonicalWeights weights) (hc0 : CanonicalConstants c0)
    (hc1 : CanonicalConstants c1) (hc2 : CanonicalConstants c2) (hout : CanonicalState out) :
    ∃ result : State,
      state_only_poseidon.interpolate_three_constant_columns_loop weights c0 c1 c2 out lane = .ok result ∧
      CanonicalState result ∧ ∀ j : Fin 16, Decode (cell result j) =
        if lane.val ≤ j.val then model weights c0 c1 c2 j else Decode (cell out j) := by
  have hwidth : poseidon2.POSEIDON2_WIDTH = 16#usize := by unfold poseidon2.POSEIDON2_WIDTH; rfl
  induction fuel generalizing out lane with
  | zero =>
    have hstop : ¬ lane < poseidon2.POSEIDON2_WIDTH := by rw [hwidth]; scalar_tac
    refine ⟨out,?_,hout,?_⟩
    · rw [generated_loop_step,if_neg hstop]
    · intro j
      have hn : ¬ lane.val ≤ j.val := by have := j.isLt; omega
      rw [if_neg hn]
  | succ fuel ih =>
    have hidx : lane.val < 16 := by omega
    have hlt : lane < poseidon2.POSEIDON2_WIDTH := by rw [hwidth]; scalar_tac
    obtain ⟨value,hstep,hcanonical,hcells⟩ := sourceStep_success weights c0 c1 c2 out lane
      hidx hw hc0 hc1 hc2 hout
    have hplusSpec : (lane + 1#usize : Result Usize) ⦃z => z.val = lane.val + 1⦄ := by
      apply UScalar.add_spec
      scalar_tac
    obtain ⟨lane1,hplus,hinc⟩ := WP.spec_imp_exists hplusSpec
    have hspan1 : lane1.val + fuel = 16 := by omega
    let out1 := out.set lane value
    obtain ⟨result,hrun,hcan,hmodel⟩ := ih out1 lane1 hspan1 hcanonical
    refine ⟨result,?_,hcan,?_⟩
    · rw [generated_loop_step,if_pos hlt,hstep]
      change (do
        let lane1 ← lane + 1#usize
        state_only_poseidon.interpolate_three_constant_columns_loop weights c0 c1 c2 out1 lane1) = .ok result
      rw [hplus]
      change state_only_poseidon.interpolate_three_constant_columns_loop weights c0 c1 c2 out1 lane1 = .ok result
      exact hrun
    · intro j
      have hv := hmodel j
      rw [hinc] at hv
      rw [hv]
      by_cases hj : j.val = lane.val
      · have hafter : ¬ lane.val + 1 ≤ j.val := by omega
        have hinside : lane.val ≤ j.val := by omega
        rw [if_neg hafter,if_pos hinside]
        have hcell := hcells j
        rw [if_pos hj] at hcell
        have hindex : (⟨lane.val,hidx⟩ : Fin 16) = j := Fin.ext hj.symm
        change Decode (cell out1 j) = model weights c0 c1 c2 ⟨lane.val,hidx⟩ at hcell
        exact hcell.trans (congrArg (model weights c0 c1 c2) hindex)
      · have hcell : Decode (cell out1 j) = Decode (cell out j) := by
          have h := hcells j
          rw [if_neg hj] at h
          exact h
        rw [hcell]
        have hrange : lane.val + 1 ≤ j.val ↔ lane.val ≤ j.val := by omega
        by_cases hin : lane.val ≤ j.val
        · rw [if_pos (hrange.mpr hin),if_pos hin]
        · have hn : ¬ lane.val + 1 ≤ j.val := fun h => hin (hrange.mp h)
          rw [if_neg hn,if_neg hin]

theorem source_success (weights : Weights) (c0 c1 c2 : Constants)
    (hw : CanonicalWeights weights) (hc0 : CanonicalConstants c0)
    (hc1 : CanonicalConstants c1) (hc2 : CanonicalConstants c2) :
    ∃ out : State, state_only_poseidon.interpolate_three_constant_columns weights c0 c1 c2 = .ok out ∧
      CanonicalState out ∧ ∀ j : Fin 16, Decode (cell out j) = model weights c0 c1 c2 j := by
  let zero : State := Array.repeat 16#usize field.QM31.ZERO
  have hzero : CanonicalState zero := by
    intro j
    have hz := AspisR1.ArrayZeroExact.repeat_zero_canonical (n := 16#usize)
    exact hz ⟨j.val,by simpa using j.isLt⟩
  obtain ⟨out,hrun,hcan,hmodel⟩ := loop_success_fuel weights c0 c1 c2 zero 0#usize 16
    (by decide) hw hc0 hc1 hc2 hzero
  refine ⟨out,?_,hcan,?_⟩
  · exact hrun
  · intro j
    have h := hmodel j
    have hstart : (0#usize).val ≤ j.val := Nat.zero_le _
    rw [if_pos hstart] at h
    exact h

#print axioms loop_success_fuel
#print axioms source_success
end AspisR1.PoseidonThreeConstantColumnsModel
