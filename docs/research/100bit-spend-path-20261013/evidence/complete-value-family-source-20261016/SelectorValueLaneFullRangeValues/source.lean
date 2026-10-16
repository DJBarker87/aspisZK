import SelectorValueLanePreprocessRangeValues
import SelectorValueLaneTailExecution
import SelectorValueLanePreprocessCanonical

/-! The actual source first populates the first 30 cells in three loops and
then writes the reconstruction/coordinate tail at 30–32. This composes those
two source contracts into a full 33-cell decoded range statement. The separate
conservation residuals and start-82 packing remain in `ValueConservationTail`.
-/
set_option autoImplicit false

namespace AspisR1.SelectorValueLaneFullRangeValues

open Aeneas Aeneas.Std Result WP
open AspisR1SelectedMaskProbe

abbrev QM := field.QM31
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact
abbrev CanonicalArray {N : Usize} (a : Array QM N) :=
  AspisR1.SelectorExpansionCorrectness.canonicalArray a
abbrev cell := AspisR1.SelectorValueLanePreprocessMeaning.cell
abbrev exactOpenings := AspisR1.SelectorValueLanePreprocessRangeValues.exactOpenings

/-- The exact decoded coordinate read used in the source tail. Naming this
coordinate keeps the output contract compact while exposing its model index. -/
def exactZ10 (openings : Openings) : ExactQM :=
  (exactOpenings openings).z ⟨10, by decide⟩


/-- Exact source prefix through the three tail writes, before selector
weighting. This exposes the actual monadic result, not just its final cells. -/
def rangePrefixConstruction (openings : Openings) : Result (Array QM 33#usize) := do
  let range0 := Array.repeat 33#usize field.QM31.ZERO
  let (openings1, range1) ← pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop0
    openings range0 0#usize
  let (openings2, range2) ← pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop1
    openings1 range1 0#usize
  let (openings3, range3) ← pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop2
    openings2 range2 0#usize
  AspisR1.SelectorValueLaneTailExecution.tailConstruction openings3 range3

private theorem cell_set_ne (a : Array QM 33#usize) (i : Usize) (x : QM)
    (j : Fin 33) (hij : j.val ≠ i.val) : cell (a.set i x) j = cell a j := by
  have hget := Array.getElem_Nat_set_ne a i j.val x (by simpa using j.isLt) hij.symm
  change AspisR1.ExtractedMaskQM31Exact.decode ((a.set i x)[j.val]) =
    AspisR1.ExtractedMaskQM31Exact.decode (a[j.val])
  exact congrArg AspisR1.ExtractedMaskQM31Exact.decode hget

private theorem cell_set_eq (a : Array QM 33#usize) (i : Usize) (x : QM)
    (j : Fin 33) (hij : j.val = i.val) : cell (a.set i x) j =
      AspisR1.ExtractedMaskQM31Exact.decode x := by
  have hget := Array.getElem_Nat_set_eq a i j.val x (by simpa using j.isLt) hij.symm
  change AspisR1.ExtractedMaskQM31Exact.decode ((a.set i x)[j.val]) =
    AspisR1.ExtractedMaskQM31Exact.decode x
  exact congrArg AspisR1.ExtractedMaskQM31Exact.decode hget

private theorem update_result_set (a : Array QM 33#usize) (i : Usize) (x : QM)
    (hi : i.val < 33) (out : Array QM 33#usize)
    (hupdate : Array.update a i x = .ok out) : out = a.set i x := by
  have hi' : i.val < a.length := by simpa [a.property] using hi
  obtain ⟨out', hrun, hset⟩ := WP.spec_imp_exists (Array.update_spec a i x hi')
  have hout : out' = out := Result.ok.inj (hrun.symm.trans hupdate)
  simpa [hout] using hset

private theorem index10_ok {a : Array QM 16#usize} :
    Array.index_usize a 10#usize = .ok (a.val[10]'(by
      simpa [a.property] using (by scalar_tac : (10#usize).val < 16))) := by
  have hb : (10#usize).val < a.length := by
    simpa [a.property] using (by scalar_tac : (10#usize).val < 16)
  obtain ⟨q, hread, hvalue⟩ := WP.spec_imp_exists (Array.index_usize_spec a 10#usize hb)
  rw [hread]
  congr 1

/-- Full generated preprocessing plus the actual three tail writes. Cells
0–29 agree with `R0P.valueRange`'s three ten-cell blocks at the same `Fin`
indices; cells 30–32 agree with the generated reconstruction and coordinate
reads. -/
theorem generated_full_range_values
    (openings : Openings)
    (hopenZ : CanonicalArray openings.z)
    (hopenSucc : CanonicalArray openings.succ_z)
    (hopenXor : CanonicalArray openings.xor12_z) :
    ∃ range1 range2 range3 reconstructed q11 q12 q13 q14 range4 range5 range6,
      pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop0
        openings (Array.repeat 33#usize field.QM31.ZERO) 0#usize = .ok (openings, range1) ∧
      pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop1
        openings range1 0#usize = .ok (openings, range2) ∧
      pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop2
        openings range2 0#usize = .ok (openings, range3) ∧
      field.QM31.sub q11 reconstructed = .ok q12 ∧
      Array.update range3 30#usize q12 = .ok range4 ∧
      Array.update range4 31#usize q13 = .ok range5 ∧
      Array.update range5 32#usize q14 = .ok range6 ∧
      rangePrefixConstruction openings = .ok range6 ∧
      (∀ i : Fin 10,
        cell range6 ⟨i.val, by omega⟩ =
          (exactOpenings openings).z (i.castAdd 6) ^ 2 -
            (exactOpenings openings).z (i.castAdd 6)) ∧
      (∀ i : Fin 10,
        cell range6 ⟨10 + i.val, by omega⟩ =
          (exactOpenings openings).succ (i.castAdd 6) ^ 2 -
            (exactOpenings openings).succ (i.castAdd 6)) ∧
      (∀ i : Fin 10,
        cell range6 ⟨20 + i.val, by omega⟩ =
          (exactOpenings openings).xor12 (i.castAdd 6) ^ 2 -
            (exactOpenings openings).xor12 (i.castAdd 6)) ∧
      cell range6 ⟨30, by omega⟩ = AspisR1.ExtractedMaskQM31Exact.decode q12 ∧
      cell range6 ⟨31, by omega⟩ = (exactOpenings openings).succ 10 ∧
      cell range6 ⟨32, by omega⟩ = (exactOpenings openings).xor12 10 ∧
      AspisR1.ExtractedMaskQM31Exact.decode q12 =
        exactZ10 openings -
          (AspisR1.SelectorValueLaneTailExecution.reconstructModel openings.z +
            AspisR1.SelectorValueLaneTailExecution.reconstructModel openings.succ_z *
              AspisR1.ExtractedMaskScalarExact.scalarEmbedding
                AspisR1.SelectorValueLaneTailExecution.scale10 +
            AspisR1.SelectorValueLaneTailExecution.reconstructModel openings.xor12_z *
              AspisR1.ExtractedMaskScalarExact.scalarEmbedding
                AspisR1.SelectorValueLaneTailExecution.scale20) ∧
      CanonicalArray range6 := by
  obtain ⟨range1, range2, range3, h0, h1, h2,
    hfirst, hsecond, hthird, hpad⟩ :=
    AspisR1.SelectorValueLanePreprocessRangeValues.preprocessing_range_values
      openings hopenZ hopenSucc hopenXor
  have hzero : CanonicalArray (Array.repeat 33#usize field.QM31.ZERO) :=
    AspisR1.SelectorValueLanePreprocessZeroInit.zero_range_canonical
  have hcanonical : CanonicalArray range3 :=
    (AspisR1.SelectorValueLanePreprocessCanonical.three_preprocessing_loops_preserve_canonicality
      openings (Array.repeat 33#usize field.QM31.ZERO)
      openings openings openings range1 range2 range3
      hopenZ hopenSucc hopenXor hzero h0 h1 h2).2
  obtain ⟨q5, q6, q7, q8, q9, q10, reconstructed, q11, q12, q13, q14,
    range4, range5, range6, hq5, hq5c, hq6, hq6c, hq7, hq7c, hq8, hq8c,
    hq9, hq9c, hq10, hq10c, hrec, hrecc, hread11, hq11c, hq12, hq12c,
    hupdate30, hread13, hq13c, hupdate31, hread14, hq14c, hupdate32,
    hrange6, hshift10, hshift20, hq12value, htailConstruction⟩ :=
    AspisR1.SelectorValueLaneTailExecution.generated_tail_execution
      openings range3 hopenZ hopenSucc hopenXor hcanonical
  have hset30 := update_result_set range3 30#usize q12 (by scalar_tac) range4 hupdate30
  have hset31 := update_result_set range4 31#usize q13 (by scalar_tac) range5 hupdate31
  have hset32 := update_result_set range5 32#usize q14 (by scalar_tac) range6 hupdate32
  have hq13val : q13 = openings.succ_z.val[10]'(by
      simpa [openings.succ_z.property] using (by scalar_tac : (10#usize).val < 16)) :=
    Result.ok.inj (hread13.symm.trans (index10_ok (a := openings.succ_z)))
  have hq14val : q14 = openings.xor12_z.val[10]'(by
      simpa [openings.xor12_z.property] using (by scalar_tac : (10#usize).val < 16)) :=
    Result.ok.inj (hread14.symm.trans (index10_ok (a := openings.xor12_z)))
  have hq11idx : q11 = openings.z.val[10]'(by
      simpa [openings.z.property] using (by scalar_tac : (10#usize).val < 16)) :=
    Result.ok.inj (hread11.symm.trans (index10_ok (a := openings.z)))
  have hq11exact : AspisR1.ExtractedMaskQM31Exact.decode q11 =
      exactZ10 openings := by
    rw [hq11idx]
    rfl
  have hq12value'' : AspisR1.ExtractedMaskQM31Exact.decode q12 =
      AspisR1.ExtractedMaskQM31Exact.decode q11 -
        (AspisR1.SelectorValueLaneTailExecution.reconstructModel openings.z +
         AspisR1.SelectorValueLaneTailExecution.reconstructModel openings.succ_z *
          AspisR1.ExtractedMaskScalarExact.scalarEmbedding AspisR1.SelectorValueLaneTailExecution.scale10 +
         AspisR1.SelectorValueLaneTailExecution.reconstructModel openings.xor12_z *
          AspisR1.ExtractedMaskScalarExact.scalarEmbedding AspisR1.SelectorValueLaneTailExecution.scale20) := by
    simpa only [AspisR1.SelectorValueLaneTailExecution.decode] using hq12value
  have hq12value' : AspisR1.ExtractedMaskQM31Exact.decode q12 =
      exactZ10 openings -
      (AspisR1.SelectorValueLaneTailExecution.reconstructModel openings.z +
       AspisR1.SelectorValueLaneTailExecution.reconstructModel openings.succ_z *
        AspisR1.ExtractedMaskScalarExact.scalarEmbedding AspisR1.SelectorValueLaneTailExecution.scale10 +
       AspisR1.SelectorValueLaneTailExecution.reconstructModel openings.xor12_z *
        AspisR1.ExtractedMaskScalarExact.scalarEmbedding AspisR1.SelectorValueLaneTailExecution.scale20) := by
    rw [hq12value'', hq11exact]
  have hprefixConstruction : rangePrefixConstruction openings = .ok range6 := by
    simp only [rangePrefixConstruction, h0, h1, h2, htailConstruction, bind_tc_ok]
  have h30val : (30#usize).val = 30 := by scalar_tac
  have h31val : (31#usize).val = 31 := by scalar_tac
  have h32val : (32#usize).val = 32 := by scalar_tac
  have hlt0 (i : Fin 10) : i.val < 33 := Nat.lt_trans i.isLt (by decide)
  have hlt1 (i : Fin 10) : 10 + i.val < 33 := by
    calc 10 + i.val < 10 + 10 := Nat.add_lt_add_left i.isLt 10
      _ ≤ 33 := by decide
  have hlt2 (i : Fin 10) : 20 + i.val < 33 := by
    calc 20 + i.val < 20 + 10 := Nat.add_lt_add_left i.isLt 20
      _ ≤ 33 := by decide
  refine ⟨range1, range2, range3, reconstructed, q11, q12, q13, q14,
    range4, range5, range6, h0, h1, h2, hq12, hupdate30, hupdate31, hupdate32,
    hprefixConstruction, ?_, ?_, ?_, ?_, ?_, ?_, hq12value', hrange6⟩
  · intro i
    rw [hset32, cell_set_ne range5 32#usize q14 ⟨i.val, hlt0 i⟩ (by
        change i.val ≠ (32#usize).val; rw [h32val]; omega),
      hset31, cell_set_ne range4 31#usize q13 ⟨i.val, hlt0 i⟩ (by
        change i.val ≠ (31#usize).val; rw [h31val]; omega),
      hset30, cell_set_ne range3 30#usize q12 ⟨i.val, hlt0 i⟩ (by
        change i.val ≠ (30#usize).val; rw [h30val]; omega)]
    exact hfirst i
  · intro i
    rw [hset32, cell_set_ne range5 32#usize q14 ⟨10 + i.val, hlt1 i⟩ (by
        change 10 + i.val ≠ (32#usize).val; rw [h32val]; omega),
      hset31, cell_set_ne range4 31#usize q13 ⟨10 + i.val, hlt1 i⟩ (by
        change 10 + i.val ≠ (31#usize).val; rw [h31val]; omega),
      hset30, cell_set_ne range3 30#usize q12 ⟨10 + i.val, hlt1 i⟩ (by
        change 10 + i.val ≠ (30#usize).val; rw [h30val]; omega)]
    exact hsecond i
  · intro i
    rw [hset32, cell_set_ne range5 32#usize q14 ⟨20 + i.val, hlt2 i⟩ (by
        change 20 + i.val ≠ (32#usize).val; rw [h32val]; omega),
      hset31, cell_set_ne range4 31#usize q13 ⟨20 + i.val, hlt2 i⟩ (by
        change 20 + i.val ≠ (31#usize).val; rw [h31val]; omega),
      hset30, cell_set_ne range3 30#usize q12 ⟨20 + i.val, hlt2 i⟩ (by
        change 20 + i.val ≠ (30#usize).val; rw [h30val]; omega)]
    exact hthird i
  · rw [hset32, cell_set_ne range5 32#usize q14 ⟨30, by decide⟩ (by
        change 30 ≠ (32#usize).val; rw [h32val]; decide),
      hset31, cell_set_ne range4 31#usize q13 ⟨30, by decide⟩ (by
        change 30 ≠ (31#usize).val; rw [h31val]; decide),
      hset30, cell_set_eq range3 30#usize q12 ⟨30, by decide⟩ (by
        change 30 = (30#usize).val; rw [h30val])]
  · rw [hset32, cell_set_ne range5 32#usize q14 ⟨31, by decide⟩ (by
        change 31 ≠ (32#usize).val; rw [h32val]; decide),
      hset31, cell_set_eq range4 31#usize q13 ⟨31, by decide⟩ (by
        change 31 = (31#usize).val; rw [h31val]), hq13val]
    rfl
  · rw [hset32, cell_set_eq range5 32#usize q14 ⟨32, by decide⟩ (by
      change 32 = (32#usize).val; rw [h32val]), hq14val]
    rfl

#print axioms generated_full_range_values
end AspisR1.SelectorValueLaneFullRangeValues
