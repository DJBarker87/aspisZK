import FJh_InternalStateWords

/-! Actual accumulation over the fifteen nonzero state lanes. The budget
tracks processed canonical words; the remaining sum stays symbolic. -/
set_option autoImplicit false
namespace AspisR1.FJh_InternalAccumulateState
open Aeneas Aeneas.Std Result WP
open FIq_Native
open AspisR1.FJh_Base (State CanonicalState cell)
open AspisR1.FJh_InternalClosureSums (Raw4 RawBound)
open AspisR1.FJh_InternalStateWords
open AspisV8R17.RawReducer

theorem source_loop_eq (state : State) (part : Raw4) (lane : Usize) :
    state_only_poseidon.internal_linear_lazy_loop0 state part lane =
      (if lane < poseidon2.POSEIDON2_WIDTH then do
        let q ← Array.index_usize state lane
        let words ← state_only_poseidon.extension_limbs q
        let nextPart ← state_only_poseidon.internal_linear_lazy_loop0_loop0 part words 0#usize
        let nextLane ← UScalar.add lane 1#usize
        state_only_poseidon.internal_linear_lazy_loop0 state nextPart nextLane
      else .ok part) := by
  rw [state_only_poseidon.internal_linear_lazy_loop0.eq_def]
  rfl

theorem loop_success_fuel (state : State) (part : Raw4) (lane : Usize) (fuel : Nat)
    (hstate : CanonicalState state) (hlane : 1 ≤ lane.val) (hspan : lane.val+fuel=16)
    (hbudget : ∀ j : Fin 4, (cell part j).val ≤ (lane.val-1)*(P-1)) :
    ∃ out : Raw4,
      state_only_poseidon.internal_linear_lazy_loop0 state part lane = .ok out ∧
      (∀ j : Fin 4, (cell out j).val ≤ 15*(P-1)) ∧
      ∀ j : Fin 4, (cell out j).val = (cell part j).val + remaining state lane.val fuel j := by
  have hwidth : poseidon2.POSEIDON2_WIDTH = 16#usize := by unfold poseidon2.POSEIDON2_WIDTH; rfl
  induction fuel generalizing part lane with
  | zero =>
    have hlane16 : lane.val = 16 := by omega
    have hstop : ¬ lane < poseidon2.POSEIDON2_WIDTH := by rw [hwidth]; scalar_tac
    refine ⟨part,?_,?_,?_⟩
    · rw [source_loop_eq,if_neg hstop]
    · rw [hlane16] at hbudget
      exact hbudget
    · intro j
      simp only [remaining,Nat.add_zero]
  | succ fuel ih =>
    have hidx : lane.val < 16 := by omega
    have hlt : lane < poseidon2.POSEIDON2_WIDTH := by rw [hwidth]; scalar_tac
    let index : Fin 16 := ⟨lane.val,hidx⟩
    let q := cell state index
    let words := wordVec q
    have hread : Array.index_usize state lane = .ok q := state_source_read state lane hidx
    have hwords := wordVec_canonical q (hstate index)
    have hp15 : RawBound part (15*P) := by
      intro j
      have hc : lane.val-1 ≤ 14 := by omega
      have hmul := Nat.mul_le_mul_right (P-1) hc
      have hsmall : 14*(P-1) < 15*P := by norm_num [P]
      exact Nat.lt_of_le_of_lt (hbudget j) (Nat.lt_of_le_of_lt hmul hsmall)
    obtain ⟨part1,hinner,_,hinnerModel⟩ := AspisR1.FJh_InternalAccumulateLimbs.source_success part words hp15 hwords
    have hinnerExplicit : state_only_poseidon.internal_linear_lazy_loop0_loop0 part (wordVec q) 0#usize = .ok part1 := hinner
    have hplusSpec : UScalar.add lane 1#usize ⦃z => z.val = lane.val+1⦄ := by
      apply UScalar.add_spec
      scalar_tac
    obtain ⟨lane1,hplus,hinc⟩ := WP.spec_imp_exists hplusSpec
    have hlane1 : 1 ≤ lane1.val := by omega
    have hspan1 : lane1.val+fuel=16 := by omega
    have hbudget1 : ∀ j : Fin 4, (cell part1 j).val ≤ (lane1.val-1)*(P-1) := by
      intro j
      rw [hinnerModel j]
      unfold AspisR1.FJh_InternalAccumulateLimbs.addModel
      have hc : lane1.val-1 = (lane.val-1)+1 := by omega
      rw [hc,Nat.add_mul,Nat.one_mul]
      exact Nat.add_le_add (hbudget j) (Nat.le_pred_of_lt (hwords j))
    obtain ⟨out,hrun,hfinal,hmodel⟩ := ih part1 lane1 hlane1 hspan1 hbudget1
    refine ⟨out,?_,hfinal,?_⟩
    · rw [source_loop_eq,if_pos hlt]
      simp only [hread,wordVec_source,bind_tc_ok]
      rw [hinnerExplicit,bind_tc_ok,hplus,bind_tc_ok]
      exact hrun
    · intro j
      have h := hmodel j
      rw [hinc,hinnerModel j] at h
      have hword : wordNat state lane.val j = (cell words j).val := wordNat_read state lane hidx j
      change (cell out j).val = (cell part j).val +
        (wordNat state lane.val j + remaining state (lane.val+1) fuel j)
      rw [hword,← Nat.add_assoc]
      exact h

def zero : Raw4 := Array.repeat 4#usize 0#u64

theorem zero_value (j : Fin 4) : (cell zero j).val = 0 := by
  change ((List.replicate (4#usize).val 0#u64)[j.val]'(by simpa using j.isLt)).val = 0
  rw [List.getElem_replicate]
  rfl

theorem source_success (state : State) (hstate : CanonicalState state) :
    ∃ out : Raw4,
      state_only_poseidon.internal_linear_lazy_loop0 state zero 1#usize = .ok out ∧
      RawBound out (15*P) ∧ ∀ j : Fin 4, (cell out j).val = remaining state 1 15 j := by
  have hbudget : ∀ j : Fin 4, (cell zero j).val ≤ ((1#usize).val-1)*(P-1) := by
    intro j
    rw [zero_value]
    exact Nat.zero_le _
  obtain ⟨out,hrun,hbound,hmodel⟩ := loop_success_fuel state zero 1#usize 15 hstate
    (by decide) (by decide) hbudget
  refine ⟨out,hrun,?_,?_⟩
  · intro j
    have hsmall : 15*(P-1) < 15*P := by norm_num [P]
    exact Nat.lt_of_le_of_lt (hbound j) hsmall
  · intro j
    have h := hmodel j
    rw [zero_value,Nat.zero_add] at h
    exact h

#print axioms source_loop_eq
#print axioms loop_success_fuel
#print axioms zero_value
#print axioms source_success
end AspisR1.FJh_InternalAccumulateState
