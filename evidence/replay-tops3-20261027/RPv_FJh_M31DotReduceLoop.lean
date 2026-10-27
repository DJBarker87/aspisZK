import RPv_FJh_M31DotReduceStep
import RPv_FJh_InternalLaneReassembly
import OccupancyRangeTraversal

/-! Actual four-coordinate chunk reduction and accumulation. An initially
loose traversal budget is sharpened using the exact coordinate formula. -/
set_option autoImplicit false
namespace AspisR1.FJh_M31DotReduceLoop
open Aeneas Aeneas.Std Result
open FIq_Native
open AspisR1.FJh_Base (cell)
open AspisR1.FJh_InternalClosureSums (Raw4 RawBound)
open AspisR1.FJh_InternalLaneReassembly (rawDecode)
open AspisR1.RawPoseidonRowField (decodeWords decodeWords_add decodeWords_mod)
open AspisR1.FJh_M31DotReduceStep (step)
open AspisV8R17.RawReducer (P)
abbrev Range := core.ops.range.Range Usize

def addModel (sums raw : Raw4) (j : Fin 4) : Nat := (cell sums j).val + (cell raw j).val % P

theorem source_loop_eq (iter : Range) (sums raw : Raw4) :
    field.qm31_m31_dot_loop1_loop1 iter sums raw = (do
      let (o,iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
      match o with
      | none => .ok sums
      | some index =>
        let nextSums ← step sums raw index
        field.qm31_m31_dot_loop1_loop1 iter1 nextSums raw) := by
  rw [field.qm31_m31_dot_loop1_loop1.eq_def]
  simp only [step,bind_assoc_eq,lift,bind_tc_ok]
  all_goals rfl

theorem loop_success_fuel (sums raw : Raw4) (iter : Range) (fuel n : Nat)
    (hend : iter.end.val ≤ 4) (hspan : iter.start.val+fuel=iter.end.val)
    (hcount : n+fuel ≤ 19) (hs : RawBound sums (n*P)) :
    ∃ out : Raw4, field.qm31_m31_dot_loop1_loop1 iter sums raw = .ok out ∧
      RawBound out ((n+fuel)*P) ∧ ∀ j : Fin 4, (cell out j).val =
        if iter.start.val ≤ j.val ∧ j.val < iter.end.val then addModel sums raw j
        else (cell sums j).val := by
  induction fuel generalizing sums iter n with
  | zero =>
    have hstop : iter.start.val ≥ iter.end.val := by omega
    have hnext := AspisR1.OccupancyRangeTraversal.next_done iter hstop
    refine ⟨sums,?_,?_,?_⟩
    · rw [source_loop_eq,hnext]
      rfl
    · simpa only [Nat.add_zero] using hs
    · intro j
      rw [if_neg (by omega)]
  | succ fuel ih =>
    have hactive : iter.start.val < iter.end.val := by omega
    have hidx : iter.start.val < 4 := by omega
    obtain ⟨value,hstep,hcan,hcells⟩ := AspisR1.FJh_M31DotReduceStep.source_success
      sums raw iter.start hidx n (by omega) hs
    let sums1 := sums.set iter.start value
    obtain ⟨iter1,hnext,hinc,hend1,_⟩ := AspisR1.OccupancyRangeTraversal.next_step iter hactive
    have hend' : iter1.end.val ≤ 4 := by rw [hend1]; exact hend
    have hspan' : iter1.start.val+fuel=iter1.end.val := by rw [hend1]; omega
    have hcount' : (n+1)+fuel ≤ 19 := by omega
    obtain ⟨out,hrun,hbound,hmodel⟩ := ih sums1 iter1 (n+1) hend' hspan' hcount' hcan
    refine ⟨out,?_,?_,?_⟩
    · rw [source_loop_eq,hnext]
      change (do
        let nextSums ← step sums raw iter.start
        field.qm31_m31_dot_loop1_loop1 iter1 nextSums raw) = .ok out
      rw [hstep]
      exact hrun
    · have heq : (n+1)+fuel = n+(fuel+1) := by omega
      simpa only [heq] using hbound
    · intro j
      have h := hmodel j
      rw [hinc,hend1] at h
      rw [h]
      by_cases hj : j.val = iter.start.val
      · have hafter : ¬ (iter.start.val+1 ≤ j.val ∧ j.val < iter.end.val) := by omega
        have hinside : iter.start.val ≤ j.val ∧ j.val < iter.end.val := by omega
        rw [if_neg hafter,if_pos hinside]
        have hc := hcells j
        rw [if_pos hj] at hc
        have hindex : (⟨iter.start.val,hidx⟩ : Fin 4) = j := Fin.ext hj.symm
        change (cell sums1 j).val = addModel sums raw ⟨iter.start.val,hidx⟩ at hc
        exact hc.trans (congrArg (addModel sums raw) hindex)
      · have hc : (cell sums1 j).val = (cell sums j).val := by
          have hp := hcells j
          rw [if_neg hj] at hp
          exact hp
        unfold addModel
        rw [hc]
        have hrange : (iter.start.val+1 ≤ j.val ∧ j.val < iter.end.val) ↔
            (iter.start.val ≤ j.val ∧ j.val < iter.end.val) := by omega
        by_cases hin : iter.start.val ≤ j.val ∧ j.val < iter.end.val
        · rw [if_pos (hrange.mpr hin),if_pos hin]
        · rw [if_neg (fun h => hin (hrange.mp h)),if_neg hin]

theorem source_success (sums raw : Raw4) (n : Nat) (hn : n ≤ 15) (hs : RawBound sums (n*P)) :
    ∃ out : Raw4, field.qm31_m31_dot_loop1_loop1
        { start := 0#usize, «end» := 4#usize } sums raw = .ok out ∧
      RawBound out ((n+1)*P) ∧ rawDecode out = rawDecode sums + rawDecode raw := by
  obtain ⟨out,hrun,_,hmodel⟩ := loop_success_fuel sums raw
    { start := 0#usize, «end» := 4#usize } 4 n (by decide) (by decide) (by omega) hs
  have hvalues : ∀ j : Fin 4, (cell out j).val = addModel sums raw j := by
    intro j
    have h := hmodel j
    have hinside : (0#usize).val ≤ j.val ∧ j.val < (4#usize).val := by have := j.isLt; scalar_tac
    rw [if_pos hinside] at h
    exact h
  refine ⟨out,hrun,?_,?_⟩
  · intro j
    rw [hvalues j]
    unfold addModel
    have hs0 := hs j
    have hm : (cell raw j).val % P < P := Nat.mod_lt _ (by norm_num [P])
    rw [Nat.add_mul,Nat.one_mul]
    omega
  · have hfun : (fun j : Fin 4 => (cell out j).val) =
        (fun j => (cell sums j).val + (cell raw j).val % P) := funext hvalues
    exact (congrArg decodeWords hfun).trans
      ((decodeWords_add (fun j : Fin 4 => (cell sums j).val)
        (fun j : Fin 4 => (cell raw j).val % P)).trans
        (congrArg (rawDecode sums + ·) (decodeWords_mod (fun j : Fin 4 => (cell raw j).val))))

#print axioms source_loop_eq
#print axioms loop_success_fuel
#print axioms source_success
end AspisR1.FJh_M31DotReduceLoop
