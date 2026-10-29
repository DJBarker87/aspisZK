import R1Z.BuilderBankStep
import R1Z.BuilderBankMerge
import R1Z.BuilderBankCollect

/-! Full bank materialization from an arbitrary well-sized Parts record.
The 16,384 writes are proved by one symbolic prefix induction. -/
set_option autoImplicit false
namespace R1Z.BuilderBankMaterialization
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open AspisBuilderGlueSource.pool_v1.pair_forest_copy_builder
open BuilderBankStep BuilderRecordsArray
attribute [local instance] Classical.propDecidable

def stableModel (pt : Parts) : Bank := tabulate 16384#usize (stableValue pt)
def lateModel (pt : Parts) : Bank := tabulate 16384#usize (lateValue pt)

theorem loop (pt : Parts) (hblocks : pt.blocks.val.length = 57)
    (iter : core.ops.range.Range Usize) (stable late : Bank)
    (hend : iter.end = 16384#usize) (hstart : iter.start.val ≤ 16384)
    (hs : Prefix stable (stableModel pt) iter.start.val)
    (hl : Prefix late (lateModel pt) iter.start.val) :
    merged_banks_loop iter pt stable late = ok (stableModel pt,lateModel pt) := by
  generalize he : 16384-iter.start.val = remaining
  induction remaining using Nat.strong_induction_on generalizing iter stable late with
  | h remaining ih =>
    by_cases hit : iter.start.val < 16384
    · obtain ⟨after,hnext,hval,hafterend⟩ := BuilderBankRange.next_some iter (by simpa [hend] using hit)
      rw [BuilderBankStep.step pt hblocks stable late iter after iter.start hit hnext]
      have hsval : stableValue pt iter.start.val = (stableModel pt).val[iter.start.val]! :=
        (tabulate_get _ _ _ (by simpa using hit)).symm
      have hlval : lateValue pt iter.start.val = (lateModel pt).val[iter.start.val]! :=
        (tabulate_get _ _ _ (by simpa using hit)).symm
      rw [hsval,hlval]
      apply ih (16384-after.start.val) (by omega) after _ _ (hafterend.trans hend) (by omega)
      · simpa only [hval] using prefix_step stable (stableModel pt) iter.start (by simpa using hit) hs
      · simpa only [hval] using prefix_step late (lateModel pt) iter.start (by simpa using hit) hl
      · rfl
    · rw [merged_banks_loop,BuilderBankRange.next_none iter (by simpa [hend] using (show 16384 ≤ iter.start.val by omega))]
      simp only [bind_tc_ok]
      have hv : iter.start.val = (16384#usize : Usize).val := by simp; omega
      rw [prefix_done stable (stableModel pt) (by simpa only [hv] using hs),
        prefix_done late (lateModel pt) (by simpa only [hv] using hl)]

theorem from_zero (pt : Parts) (hblocks : pt.blocks.val.length = 57) (stable late : Bank) :
    merged_banks_loop ⟨0#usize,16384#usize⟩ pt stable late = ok (stableModel pt,lateModel pt) :=
  loop pt hblocks _ stable late rfl (by simp)
    (by intro j hj; simp at hj) (by intro j hj; simp at hj)

/-- This isolates precisely the remaining Parts computation. Once `parts`
returns a well-sized record, every stable/late/merged cell and merge flag is
identified with the existing checked writers; no array equality is assumed. -/
theorem banks_of_parts (w : RW) (p : RP) (pt : Parts)
    (hp : parts w p = ok pt) :
    merged_banks w p = (do
      let flag ← R0WriterCopies.merge_check (stableModel pt) (lateModel pt)
      let merged ← R0WriterCopies.merge_copy (stableModel pt) (lateModel pt)
      ok (flag,stableModel pt,lateModel pt,merged)) := by
  have hblocks := BuilderBankCollect.parts_blocks_length w p pt hp
  rw [merged_banks,hp]
  simp only [bind_tc_ok]
  rw [BuilderBankMerge.source_count]
  simp only [bind_tc_ok]
  rw [from_zero pt hblocks]
  simp only [bind_tc_ok,BuilderBankMerge.check,BuilderBankMerge.copy]

/-- Actual successful Parts computation gives the full-bank std table,
including a successful merge check. This needs no semantic admission premise. -/
theorem banks_table (w : RW) (p : RP) (pt : Parts) (hp : parts w p = ok pt) :
    ∃ merged, merged_banks w p = ok (true,stableModel pt,lateModel pt,merged) ∧
      ∀ k, k < 16384 → merged.val[k]! = BuilderBankCells.cell pt (k/1024) (k%1024) := by
  let M : Nat → U32 := fun k => BuilderBankCells.cell pt (k/1024) (k%1024)
  have hs : ∀ k, k < 16384 → (stableModel pt).val[k]! = if LateRow k then 0#u32 else M k := by
    intro k hk
    exact tabulate_get _ _ _ (by simpa using hk)
  have hl : ∀ k, k < 16384 → (lateModel pt).val[k]! = if LateRow k then M k else 0#u32 := by
    intro k hk
    exact tabulate_get _ _ _ (by simpa using hk)
  obtain ⟨hcheck,merged,hmerged,hcells⟩ := merge_model M (stableModel pt) (lateModel pt) hs hl
  refine ⟨merged,?_,?_⟩
  · rw [banks_of_parts w p pt hp,hcheck]
    simp only [bind_tc_ok]
    rw [hmerged]
    rfl
  · exact hcells

#print axioms loop
#print axioms from_zero
#print axioms banks_of_parts
#print axioms banks_table
end R1Z.BuilderBankMaterialization
