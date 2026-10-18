import Aeneas
import PoseidonLeadingSourceDeclarationsV5
import PoseidonExternalPackedGroupCall
import PoseidonExternalPackedModel
import ExtractedMaskConstants
import ExtractedMaskTowerAdd
import ExtractedMaskQM31Exact
import AspisR1.PoseidonFullRoundCellStep
import R0P.Poseidon

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
open Aeneas Aeneas.Std Result
namespace AspisR1.PoseidonExternalPackedLoopModel
open AspisR1SelectedMaskProbe
open AspisR1.PoseidonFullRoundCellStep
open AspisR1.PoseidonExternalPackedGroupCall
open AspisR1.PoseidonExternalPackedModel
open AspisV8R15.ExactTowerBase (P)

abbrev State := Array field.QM31 16#usize
abbrev Packed := Array field.QM31 4#usize
abbrev Decode := AspisR1.ExtractedMaskQM31Exact.decode
abbrev CanonicalQM := AspisR1.ExtractedMaskTowerAdd.CanonicalQM

private theorem group_value_eq (x y : Usize) (h : x.val = y.val) : x = y := by
  apply UScalar.eq_of_val_eq
  exact h

private theorem group_step_success_of_bound (state : State) (packed : Packed)
    (group : Usize) (hgroup : group.val < 4) (hstate : CanonicalState state)
    (hpacked : packedCanonical packed) :
    ∃ packed1 : Packed, ∃ group1 : Usize,
      groupStep state packed group = .ok (packed1,group1) ∧
      packedCanonical packed1 ∧
      (∀ j : Fin 4, Decode (packedCell packed1 j) =
        if j.val = group.val then packedModel state ⟨group.val,hgroup⟩
        else Decode (packedCell packed j)) ∧
      group1.val = group.val + 1 := by
  let g : Fin 4 := ⟨group.val,hgroup⟩
  let group' : Usize := UScalar.ofNatCore g.val (by have := g.isLt; scalar_tac)
  have heq : group' = group := by
    apply group_value_eq
    simp [group',g,UScalar.ofNatCore_val_eq]
  obtain ⟨packed1,group1,hcall,hcan,hmodel,hgroup1⟩ :=
    groupStep_success state packed g hstate hpacked
  refine ⟨packed1,group1,?_,hcan,?_,?_⟩
  · change groupStep state packed group' = .ok (packed1,group1) at hcall
    rw [heq] at hcall
    exact hcall
  · intro j
    simpa [g] using hmodel j
  · simpa [g] using hgroup1

private theorem generated_loop_step (state : State) (packed : Packed) (group : Usize) :
    state_only_poseidon.external_linear_packed_loop state packed group =
      if group < 4#usize then do
        let (packed1,group1) ← groupStep state packed group
        state_only_poseidon.external_linear_packed_loop state packed1 group1
      else .ok packed := by
  rw [state_only_poseidon.external_linear_packed_loop.eq_def]
  by_cases h : group < 4#usize
  · simp only [h, if_pos]
    simp only [groupStep, bind_assoc_eq, bind_tc_ok] <;> rfl
  · simp [h]

private theorem initial_packed_facts :
    let packed : Packed := Array.repeat 4#usize field.QM31.ZERO
    packedCanonical packed ∧
      ∀ j : Fin 4, Decode (packedCell packed j) = 0 := by
  let packed : Packed := Array.repeat 4#usize field.QM31.ZERO
  constructor
  · intro j
    fin_cases j <;>
      simpa [packedCanonical,packedCell,packed,Array.repeat_val] using
        AspisR1.ExtractedMaskConstants.zero_canonical
  · intro j
    fin_cases j <;>
      simpa [packedCell,packed,Array.repeat_val] using
        AspisR1.ExtractedMaskConstants.zero_decode

theorem loop_success_fuel (state : State) (packed : Packed) (group : Usize)
    (fuel : Nat) (hspan : group.val + fuel = 4)
    (hstate : CanonicalState state) (hpacked : packedCanonical packed)
    (hmodel : ∀ j : Fin 4,
      Decode (packedCell packed j) =
        if j.val < group.val then packedModel state ⟨j.val,j.isLt⟩ else 0) :
    ∃ out : Packed,
      state_only_poseidon.external_linear_packed_loop state packed group = .ok out ∧
      packedCanonical out ∧
      ∀ j : Fin 4, Decode (packedCell out j) =
        if j.val < 4 then packedModel state j else 0 := by
  induction fuel generalizing packed group with
  | zero =>
      have hval : group.val = 4 := by omega
      have hstop : ¬ group < 4#usize := by scalar_tac
      refine ⟨packed,?_,hpacked,?_⟩
      · rw [generated_loop_step]
        simp [hstop]
      · intro j
        have hj : j.val < group.val := by rw [hval]; exact j.isLt
        have h := hmodel j
        rw [if_pos hj] at h
        simpa [hval] using h
  | succ fuel ih =>
      have hltVal : group.val < 4 := by omega
      have hlt : group < 4#usize := by scalar_tac
      obtain ⟨packed1,group1,hstep,hcan1,hmodel1,hgroup1⟩ :=
        group_step_success_of_bound state packed group hltVal hstate hpacked
      have hspan1 : group1.val + fuel = 4 := by rw [hgroup1]; omega
      have hmodel1' : ∀ j : Fin 4,
          Decode (packedCell packed1 j) =
            if j.val < group1.val then packedModel state ⟨j.val,j.isLt⟩ else 0 := by
        intro j
        have hsame : packedModel state ⟨group.val,hltVal⟩ =
            packedModel state (⟨group.val,hltVal⟩ : Fin 4) := rfl
        by_cases hj : j.val = group.val
        · have hnow := hmodel1 j
          rw [if_pos hj] at hnow
          rw [hnow]
          have hj1 : j.val < group1.val := by rw [hgroup1]; omega
          rw [if_pos hj1]
          have hidx : j = (⟨group.val,hltVal⟩ : Fin 4) := Fin.ext hj
          simpa [hidx]
        · have hnow := hmodel1 j
          rw [if_neg hj] at hnow
          rw [hmodel j] at hnow
          by_cases hbefore : j.val < group.val
          · have hafter : j.val < group1.val := by rw [hgroup1]; omega
            rw [if_pos hbefore] at hnow
            rw [if_pos hafter]
            exact hnow
          · have hafter : ¬ j.val < group1.val := by rw [hgroup1]; omega
            rw [if_neg hbefore] at hnow
            rw [if_neg hafter]
            exact hnow
      obtain ⟨out,hrec,hcanOut,hmodelOut⟩ :=
        ih packed1 group1 hspan1 hcan1 hmodel1'
      refine ⟨out,?_,hcanOut,?_⟩
      · rw [generated_loop_step]
        simp only [hlt,if_pos,hstep,bind_tc_ok]
        exact hrec
      · intro j
        have h := hmodelOut j
        have hj : j.val < 4 := j.isLt
        simpa [hj] using h

theorem loop_source_success (state : State) (hstate : CanonicalState state) :
    ∃ out : Packed,
      state_only_poseidon.external_linear_packed_loop state
        (Array.repeat 4#usize field.QM31.ZERO) 0#usize = .ok out ∧
      packedCanonical out ∧
      ∀ j : Fin 4, Decode (packedCell out j) = packedModel state j := by
  let packed : Packed := Array.repeat 4#usize field.QM31.ZERO
  have hinit := initial_packed_facts
  have hcan : packedCanonical packed := by simpa [packed] using hinit.1
  have hdecode : ∀ j : Fin 4, Decode (packedCell packed j) = 0 := by
    simpa [packed] using hinit.2
  have hmodel : ∀ j : Fin 4,
      Decode (packedCell packed j) =
        if j.val < 0 then packedModel state ⟨j.val,j.isLt⟩ else 0 := by
    intro j
    simp [hdecode j]
  obtain ⟨out,hrun,hcan,hmodel⟩ :=
    loop_success_fuel state packed 0#usize 4 (by decide) hstate hcan hmodel
  refine ⟨out,?_,hcan,?_⟩
  · simpa [packed] using hrun
  · intro j
    have hj : j.val < 4 := j.isLt
    simpa [hj] using hmodel j

#print axioms loop_success_fuel
#print axioms loop_source_success
end AspisR1.PoseidonExternalPackedLoopModel
