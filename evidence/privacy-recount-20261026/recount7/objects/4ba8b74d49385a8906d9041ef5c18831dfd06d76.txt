import R0Z.WriterRefinePath

/-! The extracted bank merge (copy of pair_forest_trace.rs:281-314;
DESIGN-BUILDER-MODEL §9).  `merge_copy` takes rows 544..863 from the late bank
and every other row from the stable bank; `merge_check` is true exactly when
the stable bank is zero on rows 544..863 and the late bank is zero elsewhere.
`merge_model`: if the banks are the model's cells split by row range, the
check passes and the merge is the model's column-major cell table. -/
set_option autoImplicit false

noncomputable section

namespace R0Z.WriterRefine
open Aeneas Aeneas.Std Result R0WriterCopies
attribute [local instance] Classical.propDecidable

theorem trace_cells : ∃ t : Usize, TRACE_CELLS = ok t ∧ t.val = 16384 := by
  obtain ⟨t, ht, hv⟩ := WP.spec_imp_exists
    (Usize.mul_spec (x := 16#usize) (y := 1024#usize) (by scalar_tac))
  refine ⟨t, ?_, ?_⟩
  · rw [TRACE_CELLS]; exact ht
  · rw [hv]; simp

/-- Rows 544..863 (the late bank) of the column-major flat index k. -/
def LateRow (k : Nat) : Prop := 544 ≤ k % 1024 ∧ k % 1024 < 864

instance (k : Nat) : Decidable (LateRow k) := by unfold LateRow; infer_instance

theorem rem1024 (i : Usize) : ∃ row : Usize, i % 1024#usize = ok row ∧ row.val = i.val % 1024 := by
  obtain ⟨row, hr, hv⟩ := WP.spec_imp_exists (UScalar.rem_spec i (y := 1024#usize) (by simp))
  exact ⟨row, hr, by rw [hv]; simp⟩

theorem merge_copy_loop_spec (stable late : Array U32 16384#usize) :
    ∀ (n : Nat) (i : Usize) (out : Array U32 16384#usize), i.val + n = 16384 →
      ∃ out', merge_copy_loop stable late out i = ok out' ∧
        ∀ k, out'.val[k]! = if i.val ≤ k ∧ k < 16384 then
          (if LateRow k then late.val[k]! else stable.val[k]!) else out.val[k]!
  | 0, i, out, h => by
      obtain ⟨t, ht, htv⟩ := trace_cells
      refine ⟨out, ?_, fun k => by rw [if_neg (by omega)]⟩
      rw [merge_copy_loop, ht]
      simp only [bind_tc_ok]
      rw [if_neg (by rw [UScalar.lt_equiv]; omega)]
  | n + 1, i, out, h => by
      obtain ⟨t, ht, htv⟩ := trace_cells
      obtain ⟨row, hrow, hrv⟩ := rem1024 i
      have hi1 : (Usize.wrapping_add i 1#usize).val = i.val + 1 := uadd _ _ (by scalar_tac)
      have hib : i.val < (16384#usize).val := by simp; omega
      have key : ∀ x : U32, (do
          let a ← out.update i x
          let i3 ← lift (Usize.wrapping_add i 1#usize)
          merge_copy_loop stable late a i3) =
          merge_copy_loop stable late (out.set i x) (Usize.wrapping_add i 1#usize) := by
        intro x
        rw [update_ok out i x hib]
        simp only [bind_tc_ok, lift]
      have IH : ∀ x : U32, ∃ o', merge_copy_loop stable late (out.set i x)
          (Usize.wrapping_add i 1#usize) = ok o' ∧ ∀ k, o'.val[k]! =
            if i.val + 1 ≤ k ∧ k < 16384 then (if LateRow k then late.val[k]! else stable.val[k]!)
            else (out.set i x).val[k]! := by
        intro x
        obtain ⟨o', ho', hs⟩ := merge_copy_loop_spec stable late n (Usize.wrapping_add i 1#usize)
          (out.set i x) (by rw [hi1]; omega)
        exact ⟨o', ho', fun k => by rw [hs k, hi1]⟩
      have fin : ∀ x : U32, x = (if LateRow i.val then late.val[i.val]! else stable.val[i.val]!) →
          ∀ o' : Array U32 16384#usize, (∀ k, o'.val[k]! = if i.val + 1 ≤ k ∧ k < 16384 then
            (if LateRow k then late.val[k]! else stable.val[k]!) else (out.set i x).val[k]!) →
          ∀ k, o'.val[k]! = if i.val ≤ k ∧ k < 16384 then
            (if LateRow k then late.val[k]! else stable.val[k]!) else out.val[k]! := by
        intro x hx o' hs k
        rw [hs k, set_get' out i x hib k]
        by_cases e : k = i.val
        · rw [if_neg (show ¬ (i.val + 1 ≤ k ∧ k < 16384) by omega), if_pos e,
            if_pos (show i.val ≤ k ∧ k < 16384 by omega), hx, e]
        · rw [if_neg e]
          by_cases r1 : i.val + 1 ≤ k ∧ k < 16384
          · rw [if_pos r1, if_pos (show i.val ≤ k ∧ k < 16384 by omega)]
          · rw [if_neg r1, if_neg (show ¬ (i.val ≤ k ∧ k < 16384) by omega)]
      rw [merge_copy_loop, ht]
      simp only [bind_tc_ok]
      rw [if_pos (by rw [UScalar.lt_equiv]; omega), hrow]
      simp only [bind_tc_ok]
      unfold LateRow at fin
      by_cases a : 544 ≤ i.val % 1024
      · rw [if_pos (show row >= 544#usize by rw [ge_iff_le, UScalar.le_equiv]; simp; omega)]
        by_cases b : i.val % 1024 < 864
        · rw [if_pos (show row < 864#usize by rw [UScalar.lt_equiv]; simp; omega),
            index_ok late i hib]
          simp only [bind_tc_ok]
          rw [key]
          obtain ⟨o', ho', hs⟩ := IH (late.val[i.val]!)
          exact ⟨o', ho', fin _ (by rw [if_pos ⟨a, b⟩]) o' hs⟩
        · rw [if_neg (show ¬ row < 864#usize by rw [UScalar.lt_equiv]; simp; omega),
            index_ok stable i hib]
          simp only [bind_tc_ok]
          rw [key]
          obtain ⟨o', ho', hs⟩ := IH (stable.val[i.val]!)
          exact ⟨o', ho', fin _ (by rw [if_neg (fun h => b h.2)]) o' hs⟩
      · rw [if_neg (show ¬ row >= 544#usize by rw [ge_iff_le, UScalar.le_equiv]; simp; omega),
          index_ok stable i hib]
        simp only [bind_tc_ok]
        rw [key]
        obtain ⟨o', ho', hs⟩ := IH (stable.val[i.val]!)
        exact ⟨o', ho', fin _ (by rw [if_neg (fun h => a h.1)]) o' hs⟩

/-- The shape condition from index i on. -/
def ShapeFrom (stable late : Array U32 16384#usize) (i : Nat) : Prop :=
  ∀ k, i ≤ k → k < 16384 → (if LateRow k then stable.val[k]! else late.val[k]!) = 0#u32

theorem shapeFrom_step (stable late : Array U32 16384#usize) (i : Nat) (hi : i < 16384) :
    ShapeFrom stable late i ↔
      (if LateRow i then stable.val[i]! else late.val[i]!) = 0#u32 ∧ ShapeFrom stable late (i + 1) := by
  constructor
  · intro h; exact ⟨h i (le_refl _) hi, fun k h1 h2 => h k (by omega) h2⟩
  · rintro ⟨h0, h⟩ k h1 h2
    by_cases e : k = i
    · subst e; exact h0
    · exact h k (by omega) h2

theorem merge_check_loop_spec (stable late : Array U32 16384#usize) :
    ∀ (n : Nat) (i : Usize) (ok1 : Bool), i.val + n = 16384 →
      merge_check_loop stable late ok1 i =
        ok (ok1 && decide (ShapeFrom stable late i.val))
  | 0, i, ok1, h => by
      obtain ⟨t, ht, htv⟩ := trace_cells
      rw [merge_check_loop, ht]
      simp only [bind_tc_ok]
      rw [if_neg (by rw [UScalar.lt_equiv]; omega)]
      have : ShapeFrom stable late i.val := fun k h1 h2 => by omega
      rw [decide_eq_true this, Bool.and_true]
  | n + 1, i, ok1, h => by
      obtain ⟨t, ht, htv⟩ := trace_cells
      obtain ⟨row, hrow, hrv⟩ := rem1024 i
      have hi1 : (Usize.wrapping_add i 1#usize).val = i.val + 1 := uadd _ _ (by scalar_tac)
      have hib : i.val < (16384#usize).val := by simp; omega
      have IH : ∀ b : Bool, merge_check_loop stable late b (Usize.wrapping_add i 1#usize) =
          ok (b && decide (ShapeFrom stable late (i.val + 1))) := by
        intro b; rw [merge_check_loop_spec stable late n _ _ (by rw [hi1]; omega), hi1]
      have hc : ∀ x : U32, x = (if LateRow i.val then stable.val[i.val]! else late.val[i.val]!) →
          (if (x != 0#u32) = true then (do
              let i2 ← lift (Usize.wrapping_add i 1#usize)
              merge_check_loop stable late false i2) else (do
              let i2 ← lift (Usize.wrapping_add i 1#usize)
              merge_check_loop stable late ok1 i2)) = ok (ok1 && decide (ShapeFrom stable late i.val)) := by
        intro x hx
        have st := shapeFrom_step stable late i.val (by omega)
        by_cases h0 : x = 0#u32
        · rw [if_neg (by simp [h0])]
          simp only [bind_tc_ok, lift]
          rw [IH]
          congr 2
          exact decide_eq_decide.mpr ⟨fun hs => st.2 ⟨hx ▸ h0, hs⟩, fun hs => (st.1 hs).2⟩
        · rw [if_pos (by simpa using h0)]
          simp only [bind_tc_ok, lift]
          rw [IH]
          have : ¬ ShapeFrom stable late i.val := fun hs => h0 (hx ▸ (st.1 hs).1)
          rw [decide_eq_false this]
          simp
      rw [merge_check_loop, ht]
      simp only [bind_tc_ok]
      rw [if_pos (by rw [UScalar.lt_equiv]; omega), hrow]
      simp only [bind_tc_ok]
      unfold LateRow at hc
      by_cases a : 544 ≤ i.val % 1024
      · rw [if_pos (show row >= 544#usize by rw [ge_iff_le, UScalar.le_equiv]; simp; omega)]
        by_cases b : i.val % 1024 < 864
        · rw [if_pos (show row < 864#usize by rw [UScalar.lt_equiv]; simp; omega),
            index_ok stable i hib]
          simp only [bind_tc_ok]
          exact hc _ (by rw [if_pos ⟨a, b⟩])
        · rw [if_neg (show ¬ row < 864#usize by rw [UScalar.lt_equiv]; simp; omega),
            index_ok late i hib]
          simp only [bind_tc_ok]
          exact hc _ (by rw [if_neg (fun h => b h.2)])
      · rw [if_neg (show ¬ row >= 544#usize by rw [ge_iff_le, UScalar.le_equiv]; simp; omega),
          index_ok late i hib]
        simp only [bind_tc_ok]
        exact hc _ (by rw [if_neg (fun h => a h.1)])

/-- The merge refines the model's placement: banks split by row range give a
passing check and the full table. -/
theorem merge_model (M : Nat → U32) (stable late : Array U32 16384#usize)
    (hs : ∀ k, k < 16384 → stable.val[k]! = if LateRow k then 0#u32 else M k)
    (hl : ∀ k, k < 16384 → late.val[k]! = if LateRow k then M k else 0#u32) :
    merge_check stable late = ok true ∧
      ∃ out, merge_copy stable late = ok out ∧ ∀ k, k < 16384 → out.val[k]! = M k := by
  constructor
  · rw [merge_check, merge_check_loop_spec stable late 16384 0#usize true (by simp)]
    have : ShapeFrom stable late (0#usize : Usize).val := by
      intro k _ hk
      by_cases hr : LateRow k
      · rw [if_pos hr, hs k hk, if_pos hr]
      · rw [if_neg hr, hl k hk, if_neg hr]
    rw [decide_eq_true this, Bool.true_and]
  · obtain ⟨out, ho, hsp⟩ := merge_copy_loop_spec stable late 16384 0#usize
      (Array.repeat 16384#usize 0#u32) (by simp)
    refine ⟨out, by rw [merge_copy]; exact ho, fun k hk => ?_⟩
    rw [hsp k, if_pos ⟨by simp, hk⟩]
    by_cases hr : LateRow k
    · rw [if_pos hr, hl k hk, if_pos hr]
    · rw [if_neg hr, hs k hk, if_neg hr]

#print axioms trace_cells
#print axioms merge_copy_loop_spec
#print axioms merge_check_loop_spec
#print axioms merge_model
end R0Z.WriterRefine
