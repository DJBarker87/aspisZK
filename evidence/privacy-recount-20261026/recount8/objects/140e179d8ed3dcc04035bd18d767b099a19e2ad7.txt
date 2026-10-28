import R0Z.WriterRefineOcc

/-! The extracted occupancy-row writer computes the model's occupancy row
(DESIGN-BUILDER-MODEL §9): `write_occupancy_row block r occ` returns `ok`,
leaves every cell outside row r unchanged, and the lifted row-r cells are the
model's `occCell o` whenever the record lifts to `o` and the untouched cells
of row r were zero. -/
set_option autoImplicit false

namespace R0Z.WriterRefine
open Aeneas Aeneas.Std Result R0WriterCopies

/-- The cell written at row offset c by write_occupancy_row (none = untouched). -/
def occRowCell (occ : OccRecord) (c : Nat) : Option U32 :=
  if c = 0 then some occ.occupied else if c = 1 then some occ.inverse
  else if c < 10 then some (occ.commitment.val[c - 2]!)
  else if c = 10 ∧ occ.has_selected then some occ.selected else none

theorem occ_row (block : Array U32 256#usize) (r : Usize) (hr : r.val ≤ 15) (occ : OccRecord) :
    ∃ b', write_occupancy_row block r occ = ok b' ∧
      ∀ k, b'.val[k]! =
        if r.val * 16 ≤ k ∧ k < r.val * 16 + 16 then
          (occRowCell occ (k - r.val * 16)).getD (block.val[k]!)
        else block.val[k]! := by
  have hbase : (Usize.wrapping_mul r 16#usize).val = r.val * 16 := umul _ _ (by scalar_tac)
  have h1 : (Usize.wrapping_add (Usize.wrapping_mul r 16#usize) 1#usize).val = r.val * 16 + 1 := by
    rw [uadd _ _ (by scalar_tac), hbase]; simp
  have h10 : (Usize.wrapping_add (Usize.wrapping_mul r 16#usize) 10#usize).val = r.val * 16 + 10 := by
    rw [uadd _ _ (by scalar_tac), hbase]; simp
  set base := Usize.wrapping_mul r 16#usize with hb
  let b1 := block.set base occ.occupied
  let b2 := b1.set (Usize.wrapping_add base 1#usize) occ.inverse
  obtain ⟨b3, hb3, hs3⟩ := occ_loop occ.commitment base (by rw [hbase]; omega) 8 0#usize b2 (by simp)
  have hk3 : ∀ k, b3.val[k]! = if r.val * 16 + 2 ≤ k ∧ k < r.val * 16 + 10
      then occ.commitment.val[k - r.val * 16 - 2]!
      else (if k = r.val * 16 + 1 then occ.inverse else if k = r.val * 16 then occ.occupied
        else block.val[k]!) := by
    intro k
    rw [hs3 k]
    simp only [hbase, show (0#usize : Usize).val = 0 by simp, Nat.add_zero]
    split
    · rfl
    · show (b1.set (Usize.wrapping_add base 1#usize) occ.inverse).val[k]! = _
      rw [set_get _ _ _ (by rw [h1]; omega), h1]
      split
      · rfl
      · show (block.set base occ.occupied).val[k]! = _
        rw [set_get _ _ _ (by rw [hbase]; omega), hbase]
  have run : write_occupancy_row block r occ =
      (if occ.has_selected then Array.update b3 (Usize.wrapping_add base 10#usize) occ.selected
        else ok b3) := by
    rw [write_occupancy_row]
    simp only [lift, bind_tc_ok]
    rw [update_ok block _ _ (show base.val < (256#usize).val by rw [hbase]; simp; omega)]
    simp only [bind_tc_ok]
    rw [update_ok _ _ _ (show (Usize.wrapping_add base 1#usize).val < (256#usize).val by
      rw [h1]; simp; omega)]
    simp only [bind_tc_ok]
    rw [hb3]
    simp only [bind_tc_ok]
    rfl
  cases hsel : occ.has_selected
  · refine ⟨b3, by rw [run, hsel]; rfl, fun k => ?_⟩
    rw [hk3 k]
    unfold occRowCell
    simp only [hsel]
    by_cases hin : r.val * 16 ≤ k ∧ k < r.val * 16 + 16
    · rw [if_pos hin]
      by_cases e0 : k - r.val * 16 = 0
      · rw [if_pos e0, if_neg (by omega), if_neg (by omega), if_pos (by omega)]; rfl
      · by_cases e1 : k - r.val * 16 = 1
        · rw [if_neg e0, if_pos e1, if_neg (by omega), if_pos (by omega)]; rfl
        · by_cases e2 : k - r.val * 16 < 10
          · rw [if_neg e0, if_neg e1, if_pos e2, if_pos (by omega)]
            simp only [Option.getD_some]
          · rw [if_neg e0, if_neg e1, if_neg e2, if_neg (by omega), if_neg (by omega),
              if_neg (by omega)]
            simp
    · rw [if_neg hin, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  · refine ⟨b3.set (Usize.wrapping_add base 10#usize) occ.selected, ?_, fun k => ?_⟩
    · rw [run, if_pos hsel, update_ok _ _ _ (show _ < (256#usize).val by rw [h10]; simp; omega)]
    · rw [set_get _ _ _ (by rw [h10]; omega), h10, hk3 k]
      unfold occRowCell
      simp only [hsel, and_true]
      by_cases hin : r.val * 16 ≤ k ∧ k < r.val * 16 + 16
      · rw [if_pos hin]
        by_cases e10 : k = r.val * 16 + 10
        · rw [if_pos e10, if_neg (by omega), if_neg (by omega), if_neg (by omega),
            if_pos (by omega)]; rfl
        · rw [if_neg e10]
          by_cases e0 : k - r.val * 16 = 0
          · rw [if_pos e0, if_neg (by omega), if_neg (by omega), if_pos (by omega)]; rfl
          · by_cases e1 : k - r.val * 16 = 1
            · rw [if_neg e0, if_pos e1, if_neg (by omega), if_pos (by omega)]; rfl
            · by_cases e2 : k - r.val * 16 < 10
              · rw [if_neg e0, if_neg e1, if_pos e2, if_pos (by omega)]
                simp only [Option.getD_some]
              · rw [if_neg e0, if_neg e1, if_neg e2, if_neg (by omega), if_neg (by omega),
                  if_neg (by omega), if_neg (by omega)]
                rfl
      · rw [if_neg hin, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-! ### Against the model -/

variable {K : Type} [Field K]

/-- Lift of a canonical M31 cell. -/
def liftU (x : U32) : K := ((x.val : Nat) : K)

/-- The record lifts to the model's occupancy record. -/
structure OccLifts (occ : OccRecord) (o : R0Z.BuilderModel.OccAux K) : Prop where
  occupied : liftU occ.occupied = o.occupied
  inverse : liftU occ.inverse = o.inverse
  commitment : ∀ i : Fin 8, liftU (occ.commitment.val[i.val]!) = o.commitment i
  selected : (if occ.has_selected then liftU occ.selected else 0) = o.selected

/-- The extracted writer's row r equals the model's `occCell` cell by cell,
given the record lifts and the untouched cells of row r are zero. -/
theorem occ_row_model (block : Array U32 256#usize) (r : Usize) (hr : r.val ≤ 15)
    (occ : OccRecord) (o : R0Z.BuilderModel.OccAux K) (hl : OccLifts occ o)
    (hz : ∀ c, c < 16 → block.val[r.val * 16 + c]!.val = 0) :
    ∃ b', write_occupancy_row block r occ = ok b' ∧
      (∀ c : Fin 16, liftU (K := K) (b'.val[r.val * 16 + c.val]!) = R0Z.BuilderModel.occCell o c) ∧
      (∀ k, ¬ (r.val * 16 ≤ k ∧ k < r.val * 16 + 16) → b'.val[k]! = block.val[k]!) := by
  obtain ⟨b', hrun, hk⟩ := occ_row block r hr occ
  refine ⟨b', hrun, fun c => ?_, fun k hk' => by rw [hk k, if_neg hk']⟩
  rw [hk, if_pos (by omega), show r.val * 16 + c.val - r.val * 16 = c.val by omega]
  have hzc : liftU (K := K) (block.val[r.val * 16 + c.val]!) = 0 := by
    unfold liftU; rw [hz c.val c.isLt]; simp
  unfold occRowCell R0Z.BuilderModel.occCell
  by_cases e0 : c.val = 0
  · rw [if_pos e0, if_pos e0]; exact hl.occupied
  · rw [if_neg e0, if_neg e0]
    by_cases e1 : c.val = 1
    · rw [if_pos e1, if_pos e1]; exact hl.inverse
    · rw [if_neg e1, if_neg e1]
      by_cases e2 : c.val < 10
      · rw [if_pos e2, dif_pos e2]
        exact hl.commitment ⟨c.val - 2, by omega⟩
      · rw [if_neg e2, dif_neg e2]
        by_cases e10 : c.val = 10
        · rw [if_pos e10]
          have hs := hl.selected
          cases hsel : occ.has_selected
          · rw [if_neg (by simp [hsel])]
            simp only [Option.getD_none]
            rw [hzc, ← hs, hsel]; rfl
          · rw [if_pos (by simp [e10, hsel])]
            simp only [Option.getD_some]
            rw [← hs, hsel]; rfl
        · rw [if_neg e10, if_neg (by omega)]
          simp only [Option.getD_none]
          exact hzc

#print axioms occ_row
#print axioms occ_row_model
end R0Z.WriterRefine
