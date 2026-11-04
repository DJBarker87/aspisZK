import R1Z.BuilderRecordsMatrix
import R1Z.BuilderRecordsExtracted

set_option autoImplicit false
namespace R1Z.BuilderRecordsPath
open Aeneas Aeneas.Std Result AspisBuilderRecordsReference R0Z.WriterRefine
open pool_v1.pair_forest_copy_builder R1Z.BuilderRecordsArray
abbrev Input := pool_v1.pair_forest_trace.PoolV1PairForestInputNoteWitnessV1
abbrev Pair := pool_v1.pair_trace.PoolV1PairInputNoteWitnessV1
abbrev Matrix24 := Array (Array U32 8#usize) 24#usize

def siblings (input : Input) : Matrix24 := tabulate 24#usize fun l =>
  if l = 0 then
    if input.pair.selected_second then input.pair.pair_leaf.first_commitment
    else input.pair.pair_leaf.second_commitment
  else if l ≤ 20 then input.pair.membership.siblings.val[l-1]!
  else input.super_root_siblings.val[l-21]!

def bits (input : Input) : Array U32 24#usize :=
  ⟨List.ofFn (fun l : Fin (24#usize : Usize).val =>
    if l.val = 0 then core.convert.num.FromU32Bool.from input.pair.selected_second
    else if l.val ≤ 20 then
      U32.wrapping_shr input.pair.membership.index
        (U32.ofNatCore (l.val-1) (by have := l.isLt; simp at *; omega)) &&& 1#u32
    else core.convert.num.FromU32Bool.from input.super_root_directions.val[l.val-21]!), by simp⟩

theorem sub_val (level : Usize) (n : Usize) (hn : n.val ≤ level.val) :
    (Usize.wrapping_sub level n).val = level.val - n.val := by
  rw [Usize.wrapping_sub_val_eq]
  have hs := level.hBounds
  have hns := n.hBounds
  have hb : level.val < UScalar.size .Usize := by simpa [UScalar.size_def] using level.hBounds
  have hn' : n.val < UScalar.size .Usize := by simpa [UScalar.size_def] using n.hBounds
  have he : level.val + (UScalar.size .Usize - n.val) =
      level.val - n.val + UScalar.size .Usize := by omega
  rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

theorem pair_selected (p : Pair) (b : Bool) (h : p.selected_second = b) :
    { p with selected_second := b } = p := by
  rw [← h]

/-- Fill one path row; pair ownership/reborrows do not change any input field. -/
theorem lane_spec (input : Input) (sibs : Matrix24) (level lane : Usize)
    (hl : level.val < 24) (hj : lane.val ≤ 8)
    (hs : Cells sibs (siblings input) level.val lane.val) :
    ∃ s, records_reference.records_reference_with_roots_loop0_loop0
      input.super_root_siblings input.pair sibs level lane = ok (input.pair, s) ∧
      Cells s (siblings input) level.val 8 := by
  generalize eqr : 8 - lane.val = remaining
  induction remaining using Nat.strong_induction_on generalizing lane sibs with
  | h remaining ih =>
    rw [records_reference.records_reference_with_roots_loop0_loop0]
    by_cases hlt : lane.val < 8
    · rw [if_pos (by simpa [UScalar.lt_equiv] using hlt)]
      have hrow : (siblings input).val[level.val]! =
          (if level.val = 0 then
            if input.pair.selected_second then input.pair.pair_leaf.first_commitment
            else input.pair.pair_leaf.second_commitment
          else if level.val ≤ 20 then input.pair.membership.siblings.val[level.val-1]!
          else input.super_root_siblings.val[level.val-21]!) :=
        tabulate_get _ _ _ (by simpa using hl)
      by_cases hz : level = 0#usize
      · have hzero : level.val = 0 := by rw [hz]; rfl
        rw [if_pos hz]
        cases hb : input.pair.selected_second <;>
          simp only [Bool.false_eq_true, if_false, if_true, bind_tc_ok]
        · rw [index_ok _ lane (by simpa using hlt)]
          simp only [bind_tc_ok]
          have hp : { input.pair with selected_second := false } = input.pair := pair_selected _ _ hb
          rw [hp]
          simp only [hzero, hb, if_true, Bool.false_eq_true, if_false] at hrow
          rw [← hrow]
          rw [Array.index_mut_usize, index_ok_gen sibs level (by simpa using hl)]
          simp only [bind_tc_ok]
          rw [update_gen _ lane _ (by simpa using hlt)]
          simp only [bind_tc_ok, lift]
          have hn := next_val lane (by omega)
          apply ih (8 - (Usize.wrapping_add lane 1#usize).val) (by omega)
            _ (Usize.wrapping_add lane 1#usize) (by omega)
          · simpa [hn, hzero] using cells_step sibs (siblings input) level lane (by simpa using hl) hlt hs
          · rfl
        · rw [index_ok _ lane (by simpa using hlt)]
          simp only [bind_tc_ok]
          have hp : { input.pair with selected_second := true } = input.pair := pair_selected _ _ hb
          rw [hp]
          simp only [hzero, hb, if_true] at hrow
          rw [← hrow]
          rw [Array.index_mut_usize, index_ok_gen sibs level (by simpa using hl)]
          simp only [bind_tc_ok]
          rw [update_gen _ lane _ (by simpa using hlt)]
          simp only [bind_tc_ok, lift]
          have hn := next_val lane (by omega)
          apply ih (8 - (Usize.wrapping_add lane 1#usize).val) (by omega)
            _ (Usize.wrapping_add lane 1#usize) (by omega)
          · simpa [hn, hzero] using cells_step sibs (siblings input) level lane (by simpa using hl) hlt hs
          · rfl
      · have hzero : level.val ≠ 0 := fun e => hz (UScalar.eq_of_val_eq (by simpa using e))
        rw [if_neg hz]
        by_cases ht : level.val ≤ 20
        · rw [if_pos (by simpa [UScalar.le_equiv] using ht)]
          simp only [lift, bind_tc_ok]
          have hv := sub_val level 1#usize (by simp; omega)
          simp only [UScalar.ofNatCore_val_eq] at hv
          rw [index_ok_gen _ _ (by simp only [hv]; simp; omega)]
          simp only [bind_tc_ok]
          rw [index_ok _ lane (by simpa using hlt)]
          simp only [bind_tc_ok, hv]
          simp only [hzero, if_false, ht, if_true] at hrow
          rw [← hrow]
          rw [Array.index_mut_usize, index_ok_gen sibs level (by simpa using hl)]
          simp only [bind_tc_ok]
          rw [update_gen _ lane _ (by simpa using hlt)]
          simp only [bind_tc_ok, lift]
          have hn := next_val lane (by omega)
          apply ih (8 - (Usize.wrapping_add lane 1#usize).val) (by omega)
            _ (Usize.wrapping_add lane 1#usize) (by omega)
          · simpa [hn, hzero] using cells_step sibs (siblings input) level lane (by simpa using hl) hlt hs
          · rfl
        · rw [if_neg (by simpa [UScalar.le_equiv] using ht)]
          simp only [lift, bind_tc_ok]
          have hv := sub_val level 21#usize (by simp; omega)
          simp only [UScalar.ofNatCore_val_eq] at hv
          rw [index_ok_gen _ _ (by simp only [hv]; simp; omega)]
          simp only [bind_tc_ok]
          rw [index_ok _ lane (by simpa using hlt)]
          simp only [bind_tc_ok, hv]
          simp only [hzero, if_false, ht] at hrow
          rw [← hrow]
          rw [Array.index_mut_usize, index_ok_gen sibs level (by simpa using hl)]
          simp only [bind_tc_ok]
          rw [update_gen _ lane _ (by simpa using hlt)]
          simp only [bind_tc_ok, lift]
          have hn := next_val lane (by omega)
          apply ih (8 - (Usize.wrapping_add lane 1#usize).val) (by omega)
            _ (Usize.wrapping_add lane 1#usize) (by omega)
          · simpa [hn, hzero] using cells_step sibs (siblings input) level lane (by simpa using hl) hlt hs
          · rfl
    · rw [if_neg (by simpa [UScalar.lt_equiv] using hlt)]
      have e : lane.val = 8 := by omega
      exact ⟨sibs, rfl, by simpa [e] using hs⟩

theorem bits_get (input : Input) (level : Usize) (hl : level.val < 24) :
    (bits input).val[level.val]! =
      if level = 0#usize then core.convert.num.FromU32Bool.from input.pair.selected_second
      else if level ≤ 20#usize then
        U32.wrapping_shr input.pair.membership.index
          (UScalar.cast .U32 (Usize.wrapping_sub level 1#usize)) &&& 1#u32
      else core.convert.num.FromU32Bool.from input.super_root_directions.val[level.val-21]! := by
  dsimp only [bits]
  rw [List.getElem!_ofFn _ _ (by simpa using hl)]
  dsimp only
  by_cases hz : level.val = 0
  · have he : level = 0#usize := UScalar.eq_of_val_eq (by simpa using hz)
    simp only [he, UScalar.ofNatCore_val_eq, if_true]
  · have he : level ≠ 0#usize := fun e => hz (by rw [e]; rfl)
    simp only [hz, he, if_false]
    by_cases ht : level.val ≤ 20
    · have he' : level ≤ 20#usize := by simpa [UScalar.le_equiv] using ht
      simp only [ht, he', if_true]
      congr 2
      apply UScalar.eq_of_val_eq
      have hv : (Usize.wrapping_sub level 1#usize).val = level.val - 1 := by
        simpa using sub_val level 1#usize (by simp; omega)
      have hc : (UScalar.cast .U32 (Usize.wrapping_sub level 1#usize)).val = level.val - 1 := by
        rw [UScalar.cast_val_eq, hv]
        exact Nat.mod_eq_of_lt (by simp; omega)
      simpa only [U32.ofNatCore_val_eq] using hc.symm
    · have he' : ¬level ≤ 20#usize := by simpa [UScalar.le_equiv] using ht
      simp only [ht, he', if_false]

/-- One extracted outer iteration, after eliminating only its read branches. -/
theorem level_step (input : Input) (bs : Array U32 24#usize) (ss : Matrix24)
    (level : Usize) (hl : level.val < 24) :
    records_reference.records_reference_with_roots_loop0
      input.super_root_siblings input.super_root_directions input.pair bs ss level = (do
      let bs1 ← Array.update bs level (bits input).val[level.val]!
      let (p, ss1) ← records_reference.records_reference_with_roots_loop0_loop0
        input.super_root_siblings input.pair ss level 0#usize
      records_reference.records_reference_with_roots_loop0
        input.super_root_siblings input.super_root_directions p bs1 ss1
        (Usize.wrapping_add level 1#usize)) := by
  rw [records_reference.records_reference_with_roots_loop0,
    if_pos (by simpa [UScalar.lt_equiv] using hl), bits_get input level hl]
  by_cases hz : level = 0#usize
  · simp only [hz, if_true, bind_tc_ok, lift]
  · simp only [hz, if_false]
    by_cases ht : level ≤ 20#usize
    · simp only [ht, if_true, bind_tc_ok, lift]
    · simp only [ht, if_false, bind_tc_ok, lift]
      have htn : ¬level.val ≤ 20 := by simpa [UScalar.le_equiv] using ht
      have hv := sub_val level 21#usize (by simp; omega)
      rw [index_ok_gen _ _ (by simp only [hv]; simp; omega)]
      simp only [bind_tc_ok, hv, UScalar.ofNatCore_val_eq]

theorem level_spec (input : Input) (bs : Array U32 24#usize) (ss : Matrix24)
    (level : Usize) (hl : level.val ≤ 24)
    (hb : Prefix bs (bits input) level.val)
    (hs : Cells ss (siblings input) level.val 0) :
    records_reference.records_reference_with_roots_loop0
      input.super_root_siblings input.super_root_directions input.pair bs ss level =
      ok (input.pair, bits input, siblings input) := by
  generalize eqr : 24 - level.val = remaining
  induction remaining using Nat.strong_induction_on generalizing level bs ss with
  | h remaining ih =>
    by_cases hlt : level.val < 24
    · rw [level_step input bs ss level hlt,
        update_gen bs level _ (by simpa using hlt)]
      simp only [bind_tc_ok]
      obtain ⟨s, hloop, hs'⟩ := lane_spec input ss level 0#usize hlt (by simp) hs
      rw [hloop]
      simp only [bind_tc_ok]
      have hn := next_val level hlt
      apply ih (24 - (Usize.wrapping_add level 1#usize).val) (by omega)
        _ _ (Usize.wrapping_add level 1#usize) (by omega)
      · simpa [hn] using prefix_step bs (bits input) level (by simpa using hlt) hb
      · simpa [hn] using cells_next s (siblings input) level.val hs'
      · rfl
    · rw [records_reference.records_reference_with_roots_loop0,
        if_neg (by simpa [UScalar.lt_equiv] using hlt)]
      have eq24 : level.val = (24#usize : Usize).val := by simp; omega
      rw [prefix_done bs (bits input) (by simpa [eq24] using hb),
        cells_done ss (siblings input) (by simpa [eq24] using hs)]

theorem from_zero (input : Input) (bs : Array U32 24#usize) (ss : Matrix24) :
    records_reference.records_reference_with_roots_loop0
      input.super_root_siblings input.super_root_directions input.pair bs ss 0#usize =
      ok (input.pair, bits input, siblings input) :=
  level_spec input bs ss 0#usize (by simp)
    (by intro j hj; simp at hj) (by intro i j hi hj hc; simp at hc)

#print axioms sub_val
#print axioms pair_selected
#print axioms lane_spec
#print axioms bits_get
#print axioms level_step
#print axioms level_spec
#print axioms from_zero
end R1Z.BuilderRecordsPath
