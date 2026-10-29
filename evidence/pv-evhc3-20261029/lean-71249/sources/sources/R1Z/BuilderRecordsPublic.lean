import R1Z.BuilderRecordsMatrix
import R1Z.BuilderRecordsExtracted

set_option autoImplicit false
namespace R1Z.BuilderRecordsPublic
open Aeneas Aeneas.Std Result AspisBuilderRecordsReference R0Z.WriterRefine
open pool_v1.pair_forest_copy_builder R1Z.BuilderRecordsArray
abbrev Snapshot := pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1
abbrev Matrix20 := Array (Array U32 8#usize) 20#usize
abbrev Roots := Array (Array U32 8#usize) 21#usize

def empty20 (empty : Roots) : Matrix20 := tabulate 20#usize (fun i => empty.val[i]!)

theorem lane_spec (s : Snapshot) (empty : Roots) (front emp : Matrix20)
    (level lane : Usize) (hl : level.val < 20) (hj : lane.val ≤ 8)
    (hf : Cells front s.frontier level.val lane.val)
    (he : Cells emp (empty20 empty) level.val lane.val) :
    ∃ f e, records_reference.records_reference_with_roots_loop2_loop0
      s empty front emp level lane = ok (s, f, e) ∧
      Cells f s.frontier level.val 8 ∧ Cells e (empty20 empty) level.val 8 := by
  generalize eqr : 8 - lane.val = remaining
  induction remaining using Nat.strong_induction_on generalizing lane front emp with
  | h remaining ih =>
    rw [records_reference.records_reference_with_roots_loop2_loop0]
    by_cases hlt : lane.val < 8
    · rw [if_pos (by simpa [UScalar.lt_equiv] using hlt)]
      rw [index_ok_gen s.frontier level (by simpa using hl)]
      simp only [bind_tc_ok]
      rw [index_ok _ lane (by simpa using hlt)]
      simp only [bind_tc_ok]
      rw [Array.index_mut_usize, index_ok_gen front level (by simpa using hl)]
      simp only [bind_tc_ok]
      rw [update_gen _ lane _ (by simpa using hlt)]
      simp only [bind_tc_ok]
      rw [index_ok_gen empty level (by simp; omega)]
      simp only [bind_tc_ok]
      rw [index_ok _ lane (by simpa using hlt)]
      simp only [bind_tc_ok]
      rw [Array.index_mut_usize, index_ok_gen emp level (by simpa using hl)]
      simp only [bind_tc_ok]
      rw [update_gen _ lane _ (by simpa using hlt)]
      simp only [bind_tc_ok, lift]
      have hn := next_val lane (by omega)
      apply ih (8 - (Usize.wrapping_add lane 1#usize).val) (by omega)
        _ _ (Usize.wrapping_add lane 1#usize) (by omega)
      · simpa [hn] using cells_step front s.frontier level lane (by simpa using hl) hlt hf
      · have ht : (empty20 empty).val[level.val]! = empty.val[level.val]! :=
          tabulate_get _ _ _ (by simpa using hl)
        rw [← ht]
        simpa [hn] using cells_step emp (empty20 empty) level lane (by simpa using hl) hlt he
      · rfl
    · rw [if_neg (by simpa [UScalar.lt_equiv] using hlt)]
      have e : lane.val = 8 := by omega
      exact ⟨front, emp, rfl, by simpa [e] using hf, by simpa [e] using he⟩

theorem level_spec (s : Snapshot) (empty : Roots) (front emp : Matrix20)
    (level : Usize) (hl : level.val ≤ 20)
    (hf : Cells front s.frontier level.val 0)
    (he : Cells emp (empty20 empty) level.val 0) :
    records_reference.records_reference_with_roots_loop2 s empty front emp level =
      ok (s, s.frontier, empty20 empty) := by
  generalize eqr : 20 - level.val = remaining
  induction remaining using Nat.strong_induction_on generalizing level front emp with
  | h remaining ih =>
    rw [records_reference.records_reference_with_roots_loop2]
    by_cases hlt : level.val < 20
    · rw [if_pos (by simpa [UScalar.lt_equiv] using hlt)]
      obtain ⟨f, e, hloop, hfront, hemp⟩ := lane_spec s empty front emp level 0#usize hlt (by simp) hf he
      rw [hloop]
      simp only [bind_tc_ok, lift]
      have hn := next_val level (by omega)
      apply ih (20 - (Usize.wrapping_add level 1#usize).val) (by omega)
        _ _ (Usize.wrapping_add level 1#usize) (by omega)
      · simpa [hn] using cells_next f s.frontier level.val hfront
      · simpa [hn] using cells_next e (empty20 empty) level.val hemp
      · rfl
    · rw [if_neg (by simpa [UScalar.lt_equiv] using hlt)]
      have eq20 : level.val = (20#usize : Usize).val := by simp; omega
      rw [cells_done front s.frontier (by simpa [eq20] using hf),
        cells_done emp (empty20 empty) (by simpa [eq20] using he)]

theorem from_zero (s : Snapshot) (empty : Roots) (front emp : Matrix20) :
    records_reference.records_reference_with_roots_loop2 s empty front emp 0#usize =
      ok (s, s.frontier, empty20 empty) :=
  level_spec s empty front emp 0#usize (by simp)
    (by intro i j hi hj hc; simp at hc) (by intro i j hi hj hc; simp at hc)

#print axioms lane_spec
#print axioms level_spec
#print axioms from_zero
end R1Z.BuilderRecordsPublic
