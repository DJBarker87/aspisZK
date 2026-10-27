import FJh_InternalAccumulateStep

/-! Symbolic fuel proof of the actual four-limb accumulator. A loose
intermediate budget is sharpened from the exact final per-cell formula. -/
set_option autoImplicit false
namespace AspisR1.FJh_InternalAccumulateLimbs
open Aeneas Aeneas.Std Result WP
open FIq_Native
open AspisR1.FJh_Base (cell)
open AspisR1.FJh_InternalClosureSums (Raw4 Words4 RawBound CanonicalWords)
open AspisR1.FJh_InternalAccumulateStep
open AspisV8R17.RawReducer

def addModel (part : Raw4) (words : Words4) (j : Fin 4) : Nat :=
  (cell part j).val + (cell words j).val

theorem loop_success_fuel (part : Raw4) (words : Words4) (limb : Usize) (fuel n : Nat)
    (hspan : limb.val + fuel = 4) (hbudget : n+fuel ≤ 19)
    (hp : RawBound part (n*P)) (hw : CanonicalWords words) :
    ∃ out : Raw4,
      state_only_poseidon.internal_linear_lazy_loop0_loop0 part words limb = .ok out ∧
      RawBound out ((n+fuel)*P) ∧ ∀ j : Fin 4, (cell out j).val =
        if limb.val ≤ j.val then addModel part words j else (cell part j).val := by
  induction fuel generalizing part limb n with
  | zero =>
    have hstop : ¬ limb < 4#usize := by scalar_tac
    refine ⟨part,?_,by simpa only [Nat.add_zero] using hp,?_⟩
    · rw [source_step,if_neg hstop]
    · intro j
      have hn : ¬ limb.val ≤ j.val := by have := j.isLt; omega
      rw [if_neg hn]
  | succ fuel ih =>
    have hi : limb.val < 4 := by omega
    have hlt : limb < 4#usize := by scalar_tac
    have hn : n ≤ 19 := by omega
    obtain ⟨value,hstep,hpart1,hcells⟩ := step_success part words limb n hi hn hp hw
    have hplusSpec : UScalar.add limb 1#usize ⦃z => z.val = limb.val+1⦄ := by
      apply UScalar.add_spec
      scalar_tac
    obtain ⟨limb1,hplus,hinc⟩ := WP.spec_imp_exists hplusSpec
    have hspan1 : limb1.val + fuel = 4 := by omega
    have hbudget1 : (n+1)+fuel ≤ 19 := by omega
    let part1 := part.set limb value
    obtain ⟨out,hrun,hbound,hmodel⟩ := ih part1 limb1 (n+1) hspan1 hbudget1 hpart1
    have heq : (n+1)+fuel = n+(fuel+1) := by omega
    rw [heq] at hbound
    refine ⟨out,?_,hbound,?_⟩
    · rw [source_step,if_pos hlt,hstep]
      change (do
        let limb1 ← UScalar.add limb 1#usize
        state_only_poseidon.internal_linear_lazy_loop0_loop0 part1 words limb1) = .ok out
      rw [hplus]
      change state_only_poseidon.internal_linear_lazy_loop0_loop0 part1 words limb1 = .ok out
      exact hrun
    · intro j
      have hv := hmodel j
      rw [hinc] at hv
      rw [hv]
      by_cases hj : j.val = limb.val
      · have hafter : ¬ limb.val+1 ≤ j.val := by omega
        have hinside : limb.val ≤ j.val := by omega
        rw [if_neg hafter,if_pos hinside]
        have hcell := hcells j
        rw [if_pos hj] at hcell
        have hindex : (⟨limb.val,hi⟩ : Fin 4) = j := Fin.ext hj.symm
        change (cell part1 j).val = addModel part words ⟨limb.val,hi⟩ at hcell
        exact hcell.trans (congrArg (addModel part words) hindex)
      · have hcell : (cell part1 j).val = (cell part j).val := by
          have h := hcells j
          rw [if_neg hj] at h
          exact h
        unfold addModel
        rw [hcell]
        have hsame : limb.val+1 ≤ j.val ↔ limb.val ≤ j.val := by omega
        by_cases hin : limb.val ≤ j.val
        · rw [if_pos (hsame.mpr hin),if_pos hin]
        · have hn : ¬ limb.val+1 ≤ j.val := fun h => hin (hsame.mp h)
          rw [if_neg hn,if_neg hin]

theorem source_success (part : Raw4) (words : Words4)
    (hp : RawBound part (15*P)) (hw : CanonicalWords words) :
    ∃ out : Raw4,
      state_only_poseidon.internal_linear_lazy_loop0_loop0 part words 0#usize = .ok out ∧
      RawBound out (16*P) ∧ ∀ j : Fin 4, (cell out j).val = addModel part words j := by
  obtain ⟨out,hrun,_,hmodel⟩ := loop_success_fuel part words 0#usize 4 15
    (by decide) (by decide) hp hw
  have hvalues : ∀ j : Fin 4, (cell out j).val = addModel part words j := by
    intro j
    have h := hmodel j
    have hstart : (0#usize).val ≤ j.val := Nat.zero_le _
    rw [if_pos hstart] at h
    exact h
  refine ⟨out,hrun,?_,hvalues⟩
  intro j
  rw [hvalues j]
  unfold addModel
  have hsum := Nat.add_lt_add (hp j) (hw j)
  have hlimit : 15*P+P = 16*P := by omega
  rw [hlimit] at hsum
  exact hsum

#print axioms loop_success_fuel
#print axioms source_success
end AspisR1.FJh_InternalAccumulateLimbs
