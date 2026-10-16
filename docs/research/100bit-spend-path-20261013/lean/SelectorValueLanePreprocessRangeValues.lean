import SelectorValueLanePreprocessMeaning
import R0P.Value

/-! Concrete zero-initialized composition of the three actual preprocessing
loops. The conclusion states each of the 30 populated cells against decoded
opening-array indices; the separate three-cell conservation tail is handled
by `ValueConservationTail`. -/
set_option autoImplicit false

namespace AspisR1.SelectorValueLanePreprocessRangeValues

open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe

abbrev QM := field.QM31
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact
abbrev CanonicalArray {N : Usize} (a : Array QM N) :=
  AspisR1.SelectorExpansionCorrectness.canonicalArray a

def exactOpenings (openings : Openings) : R0P.Openings ExactQM where
  z := fun i => AspisR1.ExtractedMaskQM31Exact.decode
    (openings.z.val[i.val]'(by simpa [openings.z.property] using i.isLt))
  succ := fun i => AspisR1.ExtractedMaskQM31Exact.decode
    (openings.succ_z.val[i.val]'(by simpa [openings.succ_z.property] using i.isLt))
  xor12 := fun i => AspisR1.ExtractedMaskQM31Exact.decode
    (openings.xor12_z.val[i.val]'(by simpa [openings.xor12_z.property] using i.isLt))

private theorem zero_decode :
    AspisR1.ExtractedMaskQM31Exact.decode field.QM31.ZERO = (0 : ExactQM) := by
  change AspisR1.ExtractedMaskQM31Exact.decode field.QM31.ZERO = (0 : ExactQM)
  ext <;> simp [AspisR1.ExtractedMaskQM31Exact.decode, field.QM31.ZERO]

private theorem castAdd_value (i : Fin 10) : (i.castAdd 6).val = i.val := rfl

/-- Actual loop0/1/2 execution on the source zero range populates exactly the
three ten-cell model blocks. The theorem exposes every cell value without
unfolding the generated loops beyond the symbolic interval invariants. -/
theorem preprocessing_range_values
    (openings : Openings)
    (hopenZ : CanonicalArray openings.z)
    (hopenSucc : CanonicalArray openings.succ_z)
    (hopenXor : CanonicalArray openings.xor12_z) :
    ∃ range1 range2 range3,
      pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop0
        openings (Array.repeat 33#usize field.QM31.ZERO) 0#usize = .ok (openings, range1) ∧
      pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop1
        openings range1 0#usize = .ok (openings, range2) ∧
      pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop2
        openings range2 0#usize = .ok (openings, range3) ∧
      (∀ i : Fin 10,
        AspisR1.SelectorValueLanePreprocessMeaning.cell range3 ⟨i.val, by omega⟩ =
          (exactOpenings openings).z (i.castAdd 6) ^ 2 -
            (exactOpenings openings).z (i.castAdd 6)) ∧
      (∀ i : Fin 10,
        AspisR1.SelectorValueLanePreprocessMeaning.cell range3 ⟨10 + i.val, by omega⟩ =
          (exactOpenings openings).succ (i.castAdd 6) ^ 2 -
            (exactOpenings openings).succ (i.castAdd 6)) ∧
      (∀ i : Fin 10,
        AspisR1.SelectorValueLanePreprocessMeaning.cell range3 ⟨20 + i.val, by omega⟩ =
          (exactOpenings openings).xor12 (i.castAdd 6) ^ 2 -
            (exactOpenings openings).xor12 (i.castAdd 6)) ∧
      (∀ j : Fin 33, 30 ≤ j.val →
        AspisR1.SelectorValueLanePreprocessMeaning.cell range3 j = 0) := by
  let initial : Array QM 33#usize := Array.repeat 33#usize field.QM31.ZERO
  have hspan0 : (0#usize).val + 10 = 10 := rfl
  obtain ⟨range1, hrun0, h0first, h0rest⟩ :=
    AspisR1.SelectorValueLanePreprocessMeaning.loop0_interval
      10 openings initial initial 0#usize hspan0
      (by intro j hj; omega)
      (by intro j hj; rfl) hopenZ
  obtain ⟨range2, hrun1, h1prefix, h1middle, h1rest⟩ :=
    AspisR1.SelectorValueLanePreprocessMeaning.loop1_interval
      10 openings range1 range1 0#usize hspan0
      (by intro j hj; rfl)
      (by intro j hjlo hjhi; omega)
      (by intro j hj; rfl) hopenSucc
  obtain ⟨range3, hrun2, h2prefix, h2middle, h2rest⟩ :=
    AspisR1.SelectorValueLanePreprocessMeaning.loop2_interval
      10 openings range2 range2 0#usize hspan0
      (by intro j hj; rfl)
      (by intro j hjlo hjhi; omega)
      (by intro j hj; rfl) hopenXor
  have hzrange : ∀ j : Fin 33,
      AspisR1.SelectorValueLanePreprocessMeaning.cell initial j = 0 := by
    intro j
    change AspisR1.ExtractedMaskQM31Exact.decode
      ((List.replicate 33 field.QM31.ZERO)[j.val]'(by
        simpa [initial, Array.repeat_val] using j.isLt)) = 0
    rw [List.getElem_replicate]
    exact zero_decode
  refine ⟨range1, range2, range3, hrun0, hrun1, hrun2, ?_, ?_, ?_, ?_⟩
  · intro i
    have hi : i.val < 10 := i.isLt
    let j : Fin 33 := ⟨i.val, by omega⟩
    have hj20 : j.val < 20 := by simpa [j] using Nat.lt_trans hi (by decide : 10 < 20)
    have h := h2prefix j hj20
    rw [h1prefix j hi] at h
    rw [h0first j hi] at h
    simpa [j, exactOpenings, castAdd_value,
      AspisR1.SelectorValueLanePreprocessMeaning.squareMinus, pow_two] using h
  · intro i
    have hj : 10 + i.val < 20 := by omega
    let j : Fin 33 := ⟨10 + i.val, by omega⟩
    have h := h2prefix j (by simpa [j] using hj)
    rw [h1middle j (by simp [j]) (by simpa [j] using hj)] at h
    simpa [j, exactOpenings, castAdd_value,
      AspisR1.SelectorValueLanePreprocessMeaning.squareMinus, pow_two] using h
  · intro i
    have hj : 20 + i.val < 30 := by omega
    let j : Fin 33 := ⟨20 + i.val, by omega⟩
    have h := h2middle j (by simp [j]) (by simpa [j] using hj)
    simpa [j, exactOpenings, castAdd_value,
      AspisR1.SelectorValueLanePreprocessMeaning.squareMinus, pow_two] using h
  · intro j hj
    rw [h2rest j (by omega)]
    rw [h1rest j (by omega)]
    rw [h0rest j (by omega)]
    exact hzrange j

#print axioms preprocessing_range_values
end AspisR1.SelectorValueLanePreprocessRangeValues
