import PoseidonExternalLoop1Step
import PoseidonExternalLoop1Source
import AspisR1.PoseidonFullRoundCellStep

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace AspisR1.PoseidonExternalLoop1Fuel
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PoseidonExternalLoop1Source
open AspisR1.PoseidonExternalLoop1Step
open AspisR1.PoseidonExternalColumn1Reassembly (sumWords)
open AspisR1.PoseidonFullRoundCellStep

abbrev State := Array field.QM31 16#usize
abbrev Sums := Array (Array Std.U64 4#usize) 4#usize
abbrev Decode := AspisR1.ExtractedMaskQM31Exact.decode
abbrev Exact := AspisR1.ExtractedMaskQM31Exact.QM31Exact
abbrev Canonical := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
abbrev Index := Fin (↑(16#usize))
def narrow (i : Index) : Fin 16 := ⟨i.val, by
  have hlen : (↑(16#usize) : Nat) = 16 := by decide
  omega
⟩
theorem cell_narrow_eq (a : State) (i : Index) : cell a i = cell a (narrow i) := by rfl

def incrementAt (sums : Sums) (lane : Index) : Exact :=
  AspisR1.RawPoseidonRowField.decodeWords
    (sumWords sums ⟨lane.val % 4, Nat.mod_lt _ (by omega)⟩)

def loopModel (original current : State) (sums : Sums) (processed : Nat) : Prop :=
  ∀ j : Index,
    if j.val < processed then
      Decode (cell current j) = Decode (cell original j) + incrementAt sums j
    else Decode (cell current j) = Decode (cell original j)

theorem loop1_success_fuel (original current : State) (sums : Sums)
    (lane : Usize) (fuel : Nat) (hspan : lane.val + fuel = 16)
    (hinvariant : loopModel original current sums lane.val)
    (hcurrent : CanonicalState current)
    (hsums : ∀ i j : Fin 4,
      (AspisR1.PoseidonExternalColumn1Call.sumWordAt sums i j).val < 2^34) :
    ∃ out : State,
      state_only_poseidon.external_linear_lazy_loop1 current sums lane = .ok out ∧
      CanonicalState out ∧ loopModel original out sums 16 := by
  induction fuel generalizing current lane with
  | zero =>
      have hlane : lane.val = 16 := by omega
      have hwidth : poseidon2.POSEIDON2_WIDTH.val = 16 := by simp [poseidon2.POSEIDON2_WIDTH]
      have hstop : ¬ lane < poseidon2.POSEIDON2_WIDTH := by
        change ¬ lane.val < poseidon2.POSEIDON2_WIDTH.val
        rw [hwidth]
        omega
      refine ⟨current, ?_, hcurrent, ?_⟩
      · rw [AspisR1.PoseidonExternalLoop1Source.generated_loop1_step, if_neg hstop]
      · intro j
        have hprocessed := hinvariant j
        have hj : j.val < lane.val := by rw [hlane]; exact j.isLt
        simpa [loopModel, hlane, hj] using hprocessed
  | succ fuel ih =>
      have hlane : lane.val < 16 := by omega
      have hwidth : poseidon2.POSEIDON2_WIDTH.val = 16 := by simp [poseidon2.POSEIDON2_WIDTH]
      have hcontinue : lane < poseidon2.POSEIDON2_WIDTH := by
        change lane.val < poseidon2.POSEIDON2_WIDTH.val
        rw [hwidth]
        exact hlane
      obtain ⟨value,lane1,hstep,hinc,hcanonical,hnextCanonical,hvalue,hpoint⟩ :=
        AspisR1.PoseidonExternalLoop1Step.loop1_step_success
          current sums lane hlane hcurrent hsums
      have hspan' : lane1.val + fuel = 16 := by rw [hinc]; omega
      let index : Index := ⟨lane.val, by
        have hlen : (↑(16#usize) : Nat) = 16 := by decide
        omega
      ⟩
      have hvalue' : Decode value = Decode (cell current index) + incrementAt sums index := by
        have hval := hvalue
        change Decode value = Decode (cell current (narrow index)) + laneIncrement sums lane at hval
        rw [← cell_narrow_eq (a := current) index] at hval
        simpa [index, incrementAt, laneIncrement] using hval
      have hinvariant' : loopModel original (current.set lane value) sums lane1.val := by
        intro j
        have hnextLane : lane1.val = lane.val + 1 := hinc
        by_cases heq : j.val = lane.val
        · have hj : j = index := Fin.ext heq
          subst j
          have hprev : Decode (cell current index) = Decode (cell original index) := by
            have h := hinvariant index
            have hnot : ¬ index.val < lane.val := by simp [index]
            simpa [loopModel, hnot] using h
          have hset := hpoint (narrow index)
          change Decode (cell (current.set lane value) (narrow index)) =
            (if (narrow index).val = lane.val then Decode (cell current (narrow index)) + laneIncrement sums lane
             else Decode (cell current (narrow index))) at hset
          have hidx16 : (narrow index).val = lane.val := by simp [narrow, index]
          rw [if_pos hidx16] at hset
          rw [← cell_narrow_eq (a := current.set lane value) index, ← cell_narrow_eq (a := current) index] at hset
          rw [hprev] at hset
          have hnext : index.val < lane1.val := by rw [hinc]; simp [index]
          simp only [loopModel, if_pos hnext]
          simpa [index, incrementAt, laneIncrement] using hset
        · have hpoint' := hpoint (narrow j)
          change Decode (cell (current.set lane value) (narrow j)) =
            (if (narrow j).val = lane.val then Decode (cell current ⟨lane.val,hlane⟩) + laneIncrement sums lane
             else Decode (cell current (narrow j))) at hpoint'
          rw [← cell_narrow_eq (a := current.set lane value) j, ← cell_narrow_eq (a := current) j] at hpoint'
          have hneq16 : (narrow j).val ≠ lane.val := by simpa [narrow] using heq
          simp only [if_neg hneq16] at hpoint'
          by_cases hbefore : j.val < lane.val
          · have hprev := hinvariant j
            simp only [loopModel, if_pos hbefore] at hprev
            have hnext : j.val < lane1.val := by rw [hinc]; omega
            simpa [loopModel, hnext] using hpoint'.trans hprev
          · have hafter : ¬ j.val < lane1.val := by rw [hinc]; omega
            have hprev := hinvariant j
            simp only [loopModel, if_neg hbefore] at hprev
            simpa [loopModel, hafter] using hpoint'.trans hprev
      obtain ⟨out,hrec,hcan,hmodel⟩ := ih (current.set lane value) lane1 hspan'
        hinvariant' hnextCanonical
      refine ⟨out, ?_, hcan, hmodel⟩
      rw [AspisR1.PoseidonExternalLoop1Source.generated_loop1_step]
      simp only [if_pos hcontinue, hstep, bind_tc_ok]
      exact hrec

#print axioms loop1_success_fuel
end AspisR1.PoseidonExternalLoop1Fuel
