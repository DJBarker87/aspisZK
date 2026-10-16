import SelectorValueLanePreprocessExecution
import SelectorValueLanePreprocessReconstruct
import ExtractedMaskQM31Exact

/-! Source-to-model meaning of the three preprocessing loops.  This file
states the finite interval invariant at array indices, so a later caller can
use the same Fin value in the semantic `castAdd 6` coordinates. -/
set_option autoImplicit false

namespace AspisR1.SelectorValueLanePreprocessMeaning

open Aeneas Aeneas.Std Result WP
open AspisR1SelectedMaskProbe

abbrev QM := field.QM31
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact
abbrev Canonical := AspisR1.ExtractedMaskTowerAdd.CanonicalQM
abbrev CanonicalArray {N : Usize} (a : Array QM N) :=
  AspisR1.SelectorExpansionCorrectness.canonicalArray a
abbrev Loop0 := pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop0
abbrev Loop1 := pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop1
abbrev Loop2 := pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop2

def cell (a : Array QM 33#usize) (j : Fin 33) : ExactQM :=
  AspisR1.ExtractedMaskQM31Exact.decode (a.val[j.val]'(by simpa [a.property] using j.isLt))

def squareMinus (a : Array QM 16#usize) (j : Fin 10) : ExactQM :=
  let x := AspisR1.ExtractedMaskQM31Exact.decode
    (a.val[j.val]'(by simpa [a.property] using (by omega : j.val < 16)))
  x * x - x

private theorem cell_set_eq (a : Array QM 33#usize) (i : Usize) (x : QM)
    (hi : i.val < 33) (j : Fin 33) (hij : j.val = i.val) :
    cell (a.set i x) j = AspisR1.ExtractedMaskQM31Exact.decode x := by
  have hget := Array.getElem_Nat_set_eq a i j.val x (by simpa using j.isLt) hij.symm
  change AspisR1.ExtractedMaskQM31Exact.decode ((a.set i x)[j.val]) =
    AspisR1.ExtractedMaskQM31Exact.decode x
  rw [hget]

private theorem cell_set_ne (a : Array QM 33#usize) (i : Usize) (x : QM)
    (j : Fin 33) (hij : j.val ≠ i.val) : cell (a.set i x) j = cell a j := by
  have hget := Array.getElem_Nat_set_ne a i j.val x (by simpa using j.isLt) hij.symm
  change AspisR1.ExtractedMaskQM31Exact.decode ((a.set i x)[j.val]) =
    AspisR1.ExtractedMaskQM31Exact.decode (a[j.val])
  rw [hget]

private theorem square_sub_value (x : QM) (hx : Canonical x) :
    ∃ y : QM, field.QM31.square x = .ok y ∧ Canonical y ∧
      ∃ z : QM, field.QM31.sub y x = .ok z ∧ Canonical z ∧
        AspisR1.ExtractedMaskQM31Exact.decode z =
          (AspisR1.ExtractedMaskQM31Exact.decode x)^2 -
            AspisR1.ExtractedMaskQM31Exact.decode x := by
  obtain ⟨y, hsq, hy, hsqval⟩ :=
    AspisR1.ExtractedMaskQM31SquareExact.current_qm_square_exact x hx
  obtain ⟨z, hsub, hz, hsubval⟩ :=
    AspisR1.EqualityValueAdapter.current_qm_sub_exact y x hy hx
  refine ⟨y, hsq, hy, z, hsub, hz, ?_⟩
  change AspisR1.ExtractedMaskQM31Exact.decode y =
    AspisR1.ExtractedMaskQM31Exact.decode x * AspisR1.ExtractedMaskQM31Exact.decode x at hsqval
  change AspisR1.ExtractedMaskQM31Exact.decode z =
    AspisR1.ExtractedMaskQM31Exact.decode y - AspisR1.ExtractedMaskQM31Exact.decode x at hsubval
  rw [hsubval, hsqval, pow_two]

private theorem index16_get {a : Array QM 16#usize} {i : Usize}
    (hi : i.val < 10) :
    Array.index_usize a i = .ok (a.val[i.val]'(by simpa [a.property] using (Nat.lt_trans hi (by decide)))) := by
  have h16 : i.val < 16 := Nat.lt_trans hi (by decide)
  have hb : i.val < a.length := by
    simpa [a.property] using h16
  obtain ⟨q, hread, hvalue⟩ := WP.spec_imp_exists (Array.index_usize_spec a i hb)
  rw [hread]
  congr 1

/-- Loop 0's generated writes have the exact square-minus-input value on the
processed prefix and preserve the unprocessed suffix.  The `fuel` interval
starts at `index`; no concrete recurrence unrolling is used. -/
theorem loop0_interval
    (fuel : Nat) (openings : Openings)
    (initial range : Array QM 33#usize) (index : Usize)
    (hspan : index.val + fuel = 10)
    (hprefix : ∀ (j : Fin 33) (hj : j.val < index.val),
      cell range j = squareMinus openings.z ⟨j.val, by omega⟩)
    (hsuffix : ∀ (j : Fin 33) (hj : index.val ≤ j.val), cell range j = cell initial j)
    (hopen : CanonicalArray openings.z) :
    ∃ out : Array QM 33#usize,
      Loop0 openings range index = .ok (openings, out) ∧
      (∀ (j : Fin 33) (hj : j.val < 10), cell out j = squareMinus openings.z ⟨j.val, by omega⟩) ∧
      (∀ (j : Fin 33) (hj : 10 ≤ j.val), cell out j = cell initial j) := by
  induction fuel generalizing index range with
  | zero =>
      have hindex : index.val = 10 := by omega
      have hstop : ¬ index < 10#usize := by scalar_tac
      refine ⟨range, ?_, ?_, ?_⟩
      · change pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop0 openings range index = .ok (openings, range)
        rw [pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop0.eq_def]
        simp only [if_neg hstop]
      · intro j hj
        have hj' : j.val < index.val := by rw [hindex]; exact hj
        exact hprefix j hj'
      · intro j hj
        exact hsuffix j (by omega)
  | succ fuel ih =>
      have hi : index.val < 10 := by omega
      have hlt : index < 10#usize := by scalar_tac
      have hread := index16_get (a := openings.z) hi
      have hq : Canonical (openings.z.val[index.val]'(by
          simpa [openings.z.property] using (by omega : index.val < 16))) := by
        exact hopen ⟨index.val, by simpa [openings.z.property] using (by omega : index.val < 16)⟩
      obtain ⟨q1, hsq, hq1, q2, hsub, hq2, hvalue⟩ :=
        square_sub_value _ hq
      obtain ⟨range1, hupdate, hset⟩ := WP.spec_imp_exists
        (Array.update_spec range index q2 (by simpa [range.property] using (by omega : index.val < 33)))
      obtain ⟨index1, hadd, hindex1⟩ :=
        AspisR1.SelectorValueLanePreprocessExecution.increment_success index hi
      have hprefix1 : ∀ (j : Fin 33) (hj : j.val < index1.val),
          cell range1 j = squareMinus openings.z ⟨j.val, by omega⟩ := by
        intro j hj
        have hj10 : j.val < 10 := by rw [hindex1] at hj; omega
        by_cases hji : j.val = index.val
        · rw [hset]
          rw [cell_set_eq range index q2 (by omega) j hji]
          simpa [squareMinus, hji, pow_two] using hvalue
        · have hjlt : j.val < index.val := by omega
          rw [hset]
          rw [cell_set_ne range index q2 j hji]
          exact hprefix j hjlt
      have hsuffix1 : ∀ (j : Fin 33) (hj : index1.val ≤ j.val), cell range1 j = cell initial j := by
        intro j hj
        have hnot : j.val ≠ index.val := by
          intro heq
          rw [heq, hindex1] at hj
          omega
        rw [hset]
        rw [cell_set_ne range index q2 j hnot]
        exact hsuffix j (by omega)
      obtain ⟨out, hrun, hfinalPre, hfinalPost⟩ :=
        ih range1 index1 (by omega) hprefix1 hsuffix1
      refine ⟨out, ?_, hfinalPre, hfinalPost⟩
      change pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop0 openings range index = .ok (openings, out)
      rw [pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop0.eq_def]
      simp only [if_pos hlt, hread, hsq, hsub, hupdate, bind_tc_ok]
      change (do
        let index1 ← UScalar.add index 1#usize
        pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop0 openings range1 index1) =
        .ok (openings, out)
      rw [hadd, bind_tc_ok]
      exact hrun

/-- Loop 1 writes the second ten-cell block, preserving the first block and
the suffix while assigning the same square-minus-input expression. -/
theorem loop1_interval
    (fuel : Nat) (openings : Openings)
    (initial range : Array QM 33#usize) (index : Usize)
    (hspan : index.val + fuel = 10)
    (hprefix : ∀ (j : Fin 33) (hj : j.val < 10), cell range j = cell initial j)
    (hprocessed : ∀ (j : Fin 33) (hlo : 10 ≤ j.val) (hhi : j.val < 10 + index.val),
      cell range j = squareMinus openings.succ_z ⟨j.val - 10, by omega⟩)
    (hsuffix : ∀ (j : Fin 33) (hj : 10 + index.val ≤ j.val), cell range j = cell initial j)
    (hopen : CanonicalArray openings.succ_z) :
    ∃ out : Array QM 33#usize,
      Loop1 openings range index = .ok (openings, out) ∧
      (∀ (j : Fin 33) (hj : j.val < 10), cell out j = cell initial j) ∧
      (∀ (j : Fin 33) (hlo : 10 ≤ j.val) (hhi : j.val < 20),
        cell out j = squareMinus openings.succ_z ⟨j.val - 10, by omega⟩) ∧
      (∀ (j : Fin 33) (hj : 20 ≤ j.val), cell out j = cell initial j) := by
  -- The induction mirrors `loop0_interval`; source destination is `10 + index`.
  -- Detailed body is kept explicit so the generated checked offset is visible.
  induction fuel generalizing index range with
  | zero =>
      have hindex : index.val = 10 := by omega
      have hstop : ¬ index < 10#usize := by scalar_tac
      refine ⟨range, ?_, ?_, ?_, ?_⟩
      · change pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop1 openings range index = .ok (openings, range)
        rw [pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop1.eq_def]
        simp only [if_neg hstop]
      · intro j hj; exact hprefix j hj
      · intro j hj1 hj2
        have hj2' : j.val < 10 + index.val := by rw [hindex]; exact hj2
        exact hprocessed j hj1 hj2'
      · intro j hj
        have hj' : 10 + index.val ≤ j.val := by rw [hindex]; exact hj
        exact hsuffix j hj' 
  | succ fuel ih =>
      have hi : index.val < 10 := by omega
      have hlt : index < 10#usize := by scalar_tac
      have hread := index16_get (a := openings.succ_z) hi
      have hq : Canonical (openings.succ_z.val[index.val]'(by
          simpa [openings.succ_z.property] using (by omega : index.val < 16))) := by
        exact hopen ⟨index.val, by simpa [openings.succ_z.property] using (by omega : index.val < 16)⟩
      obtain ⟨q1, hsq, hq1, q2, hsub, hq2, hvalue⟩ :=
        square_sub_value _ hq
      have haddOffsetSpec : (10#usize + index : Result Usize)
          ⦃ dest => dest.val = 10 + index.val ⦄ := by
        apply UScalar.add_spec
        scalar_tac
      obtain ⟨dest, hoffset, hdest⟩ := WP.spec_imp_exists haddOffsetSpec
      obtain ⟨range1, hupdate, hset⟩ := WP.spec_imp_exists
        (Array.update_spec range dest q2 (by
          simpa [range.property, hdest] using (show 10 + index.val < 33 by omega)))
      obtain ⟨index1, hadd, hindex1⟩ :=
        AspisR1.SelectorValueLanePreprocessExecution.increment_success index hi
      have hprefix1 : ∀ (j : Fin 33) (hj : j.val < 10), cell range1 j = cell initial j := by
        intro j hj
        rw [hset]
        rw [cell_set_ne range dest q2 j (by rw [hdest]; omega)]
        exact hprefix j hj
      have hprocessed1 : ∀ (j : Fin 33) (hjlo : 10 ≤ j.val) (hjhi : j.val < 10 + index1.val),
          cell range1 j = squareMinus openings.succ_z ⟨j.val - 10, by omega⟩ := by
        intro j hjlo hjhi
        have hj10 : j.val - 10 < 10 := by rw [hindex1] at hjhi; omega
        by_cases hji : j.val = dest.val
        · rw [hset]
          rw [cell_set_eq range dest q2 (by omega) j hji]
          have hjindex : j.val - 10 = index.val := by rw [hji, hdest]; omega
          simpa [squareMinus, hjindex, pow_two] using hvalue
        · have hjold : j.val < 10 + index.val := by omega
          rw [hset]
          rw [cell_set_ne range dest q2 j hji]
          exact hprocessed j hjlo hjold
      have hsuffix1 : ∀ (j : Fin 33) (hj : 10 + index1.val ≤ j.val),
          cell range1 j = cell initial j := by
        intro j hj
        have hji : j.val ≠ dest.val := by
          intro heq
          rw [heq, hdest, hindex1] at hj
          omega
        rw [hset]
        rw [cell_set_ne range dest q2 j hji]
        exact hsuffix j (by omega)
      obtain ⟨out, hrun, hfinalPrefix, hfinalProcessed, hfinalSuffix⟩ :=
        ih range1 index1 (by omega) hprefix1 hprocessed1 hsuffix1
      refine ⟨out, ?_, hfinalPrefix, hfinalProcessed, hfinalSuffix⟩
      change pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop1 openings range index = .ok (openings, out)
      rw [pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop1.eq_def]
      simp only [if_pos hlt, hread, hsq, hsub, hoffset, hupdate, bind_tc_ok]
      change (do
        let index1 ← UScalar.add index 1#usize
        pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop1 openings range1 index1) =
        .ok (openings, out)
      rw [hadd, bind_tc_ok]
      exact hrun

/-- Loop 2 writes the third ten-cell block and preserves cells outside it. -/
theorem loop2_interval
    (fuel : Nat) (openings : Openings)
    (initial range : Array QM 33#usize) (index : Usize)
    (hspan : index.val + fuel = 10)
    (hprefix : ∀ (j : Fin 33) (hj : j.val < 20), cell range j = cell initial j)
    (hprocessed : ∀ (j : Fin 33) (hlo : 20 ≤ j.val) (hhi : j.val < 20 + index.val),
      cell range j = squareMinus openings.xor12_z ⟨j.val - 20, by omega⟩)
    (hsuffix : ∀ (j : Fin 33) (hj : 20 + index.val ≤ j.val), cell range j = cell initial j)
    (hopen : CanonicalArray openings.xor12_z) :
    ∃ out : Array QM 33#usize,
      Loop2 openings range index = .ok (openings, out) ∧
      (∀ (j : Fin 33) (hj : j.val < 20), cell out j = cell initial j) ∧
      (∀ (j : Fin 33) (hlo : 20 ≤ j.val) (hhi : j.val < 30),
        cell out j = squareMinus openings.xor12_z ⟨j.val - 20, by omega⟩) ∧
      (∀ (j : Fin 33) (hj : 30 ≤ j.val), cell out j = cell initial j) := by
  -- As above, source destination is `20 + index`.
  induction fuel generalizing index range with
  | zero =>
      have hindex : index.val = 10 := by omega
      have hstop : ¬ index < 10#usize := by scalar_tac
      refine ⟨range, ?_, ?_, ?_, ?_⟩
      · change pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop2 openings range index = .ok (openings, range)
        rw [pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop2.eq_def]
        simp only [if_neg hstop]
      · intro j hj; exact hprefix j hj
      · intro j hj1 hj2
        have hj2' : j.val < 20 + index.val := by rw [hindex]; exact hj2
        exact hprocessed j hj1 hj2'
      · intro j hj
        have hj' : 20 + index.val ≤ j.val := by rw [hindex]; exact hj
        exact hsuffix j hj' 
  | succ fuel ih =>
      have hi : index.val < 10 := by omega
      have hlt : index < 10#usize := by scalar_tac
      have hread := index16_get (a := openings.xor12_z) hi
      have hq : Canonical (openings.xor12_z.val[index.val]'(by
          simpa [openings.xor12_z.property] using (by omega : index.val < 16))) := by
        exact hopen ⟨index.val, by simpa [openings.xor12_z.property] using (by omega : index.val < 16)⟩
      obtain ⟨q1, hsq, hq1, q2, hsub, hq2, hvalue⟩ :=
        square_sub_value _ hq
      have haddOffsetSpec : (20#usize + index : Result Usize)
          ⦃ dest => dest.val = 20 + index.val ⦄ := by
        apply UScalar.add_spec
        scalar_tac
      obtain ⟨dest, hoffset, hdest⟩ := WP.spec_imp_exists haddOffsetSpec
      obtain ⟨range1, hupdate, hset⟩ := WP.spec_imp_exists
        (Array.update_spec range dest q2 (by
          simpa [range.property, hdest] using (show 20 + index.val < 33 by omega)))
      obtain ⟨index1, hadd, hindex1⟩ :=
        AspisR1.SelectorValueLanePreprocessExecution.increment_success index hi
      have hprefix1 : ∀ (j : Fin 33) (hj : j.val < 20), cell range1 j = cell initial j := by
        intro j hj
        rw [hset]
        rw [cell_set_ne range dest q2 j (by rw [hdest]; omega)]
        exact hprefix j hj
      have hprocessed1 : ∀ (j : Fin 33) (hjlo : 20 ≤ j.val) (hjhi : j.val < 20 + index1.val),
          cell range1 j = squareMinus openings.xor12_z ⟨j.val - 20, by omega⟩ := by
        intro j hjlo hjhi
        have hj10 : j.val - 20 < 10 := by rw [hindex1] at hjhi; omega
        by_cases hji : j.val = dest.val
        · rw [hset]
          rw [cell_set_eq range dest q2 (by omega) j hji]
          have hjindex : j.val - 20 = index.val := by rw [hji, hdest]; omega
          simpa [squareMinus, hjindex, pow_two] using hvalue
        · have hjold : j.val < 20 + index.val := by omega
          rw [hset]
          rw [cell_set_ne range dest q2 j hji]
          exact hprocessed j hjlo hjold
      have hsuffix1 : ∀ (j : Fin 33) (hj : 20 + index1.val ≤ j.val),
          cell range1 j = cell initial j := by
        intro j hj
        have hji : j.val ≠ dest.val := by
          intro heq
          rw [heq, hdest, hindex1] at hj
          omega
        rw [hset]
        rw [cell_set_ne range dest q2 j hji]
        exact hsuffix j (by omega)
      obtain ⟨out, hrun, hfinalPrefix, hfinalProcessed, hfinalSuffix⟩ :=
        ih range1 index1 (by omega) hprefix1 hprocessed1 hsuffix1
      refine ⟨out, ?_, hfinalPrefix, hfinalProcessed, hfinalSuffix⟩
      change pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop2 openings range index = .ok (openings, out)
      rw [pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop2.eq_def]
      simp only [if_pos hlt, hread, hsq, hsub, hoffset, hupdate, bind_tc_ok]
      change (do
        let index1 ← UScalar.add index 1#usize
        pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop2 openings range1 index1) =
        .ok (openings, out)
      rw [hadd, bind_tc_ok]
      exact hrun

#print axioms loop0_interval
#print axioms loop1_interval
#print axioms loop2_interval
end AspisR1.SelectorValueLanePreprocessMeaning
