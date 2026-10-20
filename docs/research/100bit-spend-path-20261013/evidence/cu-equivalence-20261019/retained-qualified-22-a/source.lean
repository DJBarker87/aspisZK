import AspisR1S2Groups.Funs
import CuSavingsS2Order
import Mathlib.Tactic.IntervalCases
set_option autoImplicit false
namespace AspisR1.CuSavingsS2SourceTables
open Aeneas Aeneas.Std Result AspisR1S2Groups

private theorem map_getD {ty : UScalarTy} (xs : List (UScalar ty)) (n : Nat) (hn : n < xs.length) :
    (xs.map UScalar.val).getD n 0 = (xs[n]'hn).val := by
  rw [List.getD_eq_getElem (xs.map UScalar.val) 0 (by simpa only [List.length_map] using hn)]
  rw [List.getElem_map]

theorem group_values : new.S2_INACTIVE_GROUPS.val.map UScalar.val = CuSavingsS2Tables.groups := by
  simp [new.S2_INACTIVE_GROUPS,Array.make,CuSavingsS2Tables.groups]

theorem mask_values : new.S2_INACTIVE_MASKS.val.map UScalar.val = CuSavingsS2Tables.masks := by
  simp [new.S2_INACTIVE_MASKS,Array.make,CuSavingsS2Tables.masks]

theorem active_values : r0.opening.COPY_ACTIVE_ROW_MASKS.val.map UScalar.val = CuSavingsS2Tables.active := by
  simp [r0.opening.COPY_ACTIVE_ROW_MASKS,Array.make,CuSavingsS2Tables.active]

theorem group_source (j : Usize) (hj : j.val < 64) :
    ∃ g : U8, Array.index_usize new.S2_INACTIVE_GROUPS j = .ok g ∧
      g.val=CuSavingsS2Tables.groupValue ⟨j.val,hj⟩ ∧ g.val < 12 := by
  have hlen : j.val < new.S2_INACTIVE_GROUPS.length := by simpa [new.S2_INACTIVE_GROUPS] using hj
  obtain ⟨g,hg,hv⟩ := WP.spec_imp_exists (Array.index_usize_spec new.S2_INACTIVE_GROUPS j hlen)
  have hget := map_getD new.S2_INACTIVE_GROUPS.val j.val hlen
  have he : g.val = CuSavingsS2Tables.groupValue ⟨j.val,hj⟩ :=
    (congrArg UScalar.val hv).trans (hget.symm.trans
      (congrArg (fun xs : List Nat => xs.getD j.val 0) group_values))
  exact ⟨g,hg,he,by rw [he];exact CuSavingsS2Tables.groupValue_lt ⟨j.val,hj⟩⟩

theorem mask_source (g : Usize) (hg : g.val < 12) :
    ∃ m : U16, Array.index_usize new.S2_INACTIVE_MASKS g = .ok m ∧
      m.val = CuSavingsS2Tables.masks.getD g.val 0 := by
  have hlen : g.val < new.S2_INACTIVE_MASKS.length := by simpa [new.S2_INACTIVE_MASKS] using hg
  obtain ⟨m,hm,hv⟩ := WP.spec_imp_exists (Array.index_usize_spec new.S2_INACTIVE_MASKS g hlen)
  have hget := map_getD new.S2_INACTIVE_MASKS.val g.val hlen
  exact ⟨m,hm,(congrArg UScalar.val hv).trans (hget.symm.trans
      (congrArg (fun xs : List Nat => xs.getD g.val 0) mask_values))⟩

theorem active_source (g : Usize) (hg : g.val < 64) :
    ∃ m : U16, Array.index_usize r0.opening.COPY_ACTIVE_ROW_MASKS g = .ok m ∧
      m.val = CuSavingsS2Tables.active.getD g.val 0 := by
  have hlen : g.val < r0.opening.COPY_ACTIVE_ROW_MASKS.length := by simpa [r0.opening.COPY_ACTIVE_ROW_MASKS] using hg
  obtain ⟨m,hm,hv⟩ := WP.spec_imp_exists (Array.index_usize_spec r0.opening.COPY_ACTIVE_ROW_MASKS g hlen)
  have hget := map_getD r0.opening.COPY_ACTIVE_ROW_MASKS.val g.val hlen
  exact ⟨m,hm,(congrArg UScalar.val hv).trans (hget.symm.trans
      (congrArg (fun xs : List Nat => xs.getD g.val 0) active_values))⟩

def seen (j : Nat) : Nat := (CuSavingsS2Tables.firstPositions.filter (fun x => x < j)).length

theorem catalog_step (j : Fin 64) :
    CuSavingsS2Tables.groupValue j ≤ seen j.val ∧ seen j.val ≤ 12 ∧
    seen (j.val+1) = (if CuSavingsS2Tables.groupValue j = seen j.val then seen j.val+1 else seen j.val) := by
  fin_cases j <;> decide

theorem seen_zero : seen 0 = 0 := by decide
theorem seen_end : seen 64 = 12 := by decide

theorem mask_distinct (i g : Fin 12) (h : i ≠ g) :
    CuSavingsS2Tables.masks.getD i.val 0 ≠ CuSavingsS2Tables.masks.getD g.val 0 := by
  fin_cases i <;> fin_cases g <;> simp_all [CuSavingsS2Tables.masks]

#print axioms group_values
#print axioms mask_values
#print axioms active_values
#print axioms group_source
#print axioms mask_source
#print axioms active_source
#print axioms catalog_step
#print axioms mask_distinct
end AspisR1.CuSavingsS2SourceTables
