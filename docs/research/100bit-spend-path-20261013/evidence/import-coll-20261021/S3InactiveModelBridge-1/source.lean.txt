import S3S9CurrentSourceModel
import AspisR1S3InactiveSource.Funs
import S3InactiveExecutionBridge

set_option autoImplicit false
namespace AspisR1.S3InactiveModelBridge

open Aeneas Aeneas.Std Result WP

def extractedActiveMasks : List Nat :=
  AspisR1S3InactiveSource.r0.opening.COPY_ACTIVE_ROW_MASKS.val.map UScalar.val

/-- The 64 masks emitted for the actual `COPY_ACTIVE_ROW_MASKS` constant are
exactly the mask literals used by the S3 mathematical model. -/
theorem extracted_masks_eq_model :
    extractedActiveMasks = AspisR1.S3S9CurrentSourceModel.activeRowMasks := by
  unfold extractedActiveMasks
  delta AspisR1S3InactiveSource.r0.opening.COPY_ACTIVE_ROW_MASKS
  simp [AspisR1.S3S9CurrentSourceModel.activeRowMasks,
    Aeneas.Std.Array.make, Aeneas.Std.UScalar.ofNatCore_val_eq]

theorem extracted_mask_value_eq_model (i : Aeneas.Std.Usize) (mask : Aeneas.Std.U16)
    (hi : i.val < 64)
    (hread : AspisR1S3InactiveSource.r0.opening.COPY_ACTIVE_ROW_MASKS.index_usize i = .ok mask) :
    mask.val = AspisR1.S3S9CurrentSourceModel.activeRowMasks.getD i.val 0 := by
  have hbound : i.val < AspisR1S3InactiveSource.r0.opening.COPY_ACTIVE_ROW_MASKS.length := by
    simp only [Aeneas.Std.Array.length]
    have hlen := AspisR1S3InactiveSource.r0.opening.COPY_ACTIVE_ROW_MASKS.property
    rw [hlen]
    simpa [Aeneas.Std.UScalar.ofNatCore_val_eq] using hi
  obtain ⟨x, hx, hxval⟩ := WP.spec_imp_exists
    (Aeneas.Std.Array.index_usize_spec
      AspisR1S3InactiveSource.r0.opening.COPY_ACTIVE_ROW_MASKS i hbound)
  have hxmask : x = mask := by
    rw [hread] at hx
    exact (Result.ok.inj hx).symm
  have htable := congrArg (fun xs : List Nat => xs.getD i.val 0) extracted_masks_eq_model
  have htable' : (AspisR1S3InactiveSource.r0.opening.COPY_ACTIVE_ROW_MASKS.val.map
      Aeneas.Std.UScalar.val).getD i.val 0 =
      AspisR1.S3S9CurrentSourceModel.activeRowMasks.getD i.val 0 := by
    exact htable
  have hidx : i.val < AspisR1S3InactiveSource.r0.opening.COPY_ACTIVE_ROW_MASKS.val.length := by
    have hp := AspisR1S3InactiveSource.r0.opening.COPY_ACTIVE_ROW_MASKS.property
    rw [hp]
    simpa [Aeneas.Std.UScalar.ofNatCore_val_eq] using hi
  have hmapped : i.val < (AspisR1S3InactiveSource.r0.opening.COPY_ACTIVE_ROW_MASKS.val.map
      Aeneas.Std.UScalar.val).length := by simpa using hidx
  have hmapget : (AspisR1S3InactiveSource.r0.opening.COPY_ACTIVE_ROW_MASKS.val.map
      Aeneas.Std.UScalar.val).getD i.val 0 = x.val := by
    rw [List.getD_eq_getElem _ _ hmapped, List.getElem_map, hxval]
  calc
    mask.val = x.val := congrArg Aeneas.Std.UScalar.val hxmask.symm
    _ = (AspisR1S3InactiveSource.r0.opening.COPY_ACTIVE_ROW_MASKS.val.map
        Aeneas.Std.UScalar.val).getD i.val 0 := hmapget.symm
    _ = AspisR1.S3S9CurrentSourceModel.activeRowMasks.getD i.val 0 := htable'

private theorem shifted_low_bit_eq_div_mod (x k : Nat) :
    ((x >>> k) &&& 1) = (x / 2^k) % 2 := by
  rw [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]

/-- For every in-range row, the actual extracted Rust helper returns exactly
the source model's inactive predicate, using the same extracted mask table. -/
theorem actual_inactive_eq_source_model (r : Aeneas.Std.Usize)
    (hr : r.val < 1024) :
    ∃ i mask,
      i.val = r.val / 16 ∧
      AspisR1S3InactiveSource.r0.opening.COPY_ACTIVE_ROW_MASKS.index_usize i = .ok mask ∧
      AspisR1S3InactiveSource.r0.opening.inactive r =
        .ok (core.result.Result.Ok
          (decide (AspisR1.S3S9CurrentSourceModel.sourceInactive r.val = 1))) := by
  have hbelow : ¬ r ≥ 1024#usize := by
    change ¬ 1024#usize ≤ r
    change ¬ (1024#usize).val ≤ r.val
    norm_num [UScalar.ofNatCore_val_eq]
    omega
  obtain ⟨i, mask, hindex, hread, hout⟩ :=
    AspisR1.S3InactiveExecutionBridge.inactive_mask_exec_spec r hbelow hr
  have hmask := extracted_mask_value_eq_model i mask (by omega) hread
  have hbit :
      AspisR1.S3InactiveExecutionBridge.inactiveMaskBit mask r =
        decide (AspisR1.S3S9CurrentSourceModel.sourceInactive r.val = 1) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    unfold AspisR1.S3InactiveExecutionBridge.inactiveMaskBit
    simp only [decide_eq_true_eq]
    rw [shifted_low_bit_eq_div_mod, hmask, hindex]
    unfold AspisR1.S3S9CurrentSourceModel.sourceInactive
      AspisR1.S3S9CurrentSourceModel.bitAt
    omega
  exact ⟨i, mask, hindex, hread, by rw [hout, hbit]⟩

/-- The extracted helper, evaluated at any Usize carrying a source row, agrees
with the exact grouped S3 classification. The row-construction equality is
kept explicit for the caller. -/
theorem actual_inactive_eq_grouped_model
    (r : Aeneas.Std.Usize) (j : Fin 64) (s : Fin 16)
    (hrow : r.val = AspisR1.S3S9CurrentSourceModel.s2Row (16*j.val+s.val)) :
    AspisR1S3InactiveSource.r0.opening.inactive r =
      .ok (core.result.Result.Ok
        (AspisR1.S3S9CurrentSourceModel.inactiveAtGroup
          (AspisR1.S3S9CurrentSourceModel.groupAt j) s)) := by
  have hbound := AspisR1.S3S9CurrentSourceModel.s2_row_range j s
  obtain ⟨i, mask, hi, hread, hout⟩ := actual_inactive_eq_source_model r (by rw [hrow]; exact hbound)
  have hclass :
      decide (AspisR1.S3S9CurrentSourceModel.sourceInactive r.val = 1) =
        AspisR1.S3S9CurrentSourceModel.inactiveAtGroup
          (AspisR1.S3S9CurrentSourceModel.groupAt j) s := by
    rw [hrow]
    simpa [AspisR1.S3S9CurrentSourceModel.inactiveAtSource] using
      (AspisR1.S3S9CurrentSourceModel.s3_group_classification j s)
  rw [hout, hclass]

#print axioms extracted_masks_eq_model
#print axioms extracted_mask_value_eq_model
#print axioms actual_inactive_eq_source_model
#print axioms actual_inactive_eq_grouped_model
end AspisR1.S3InactiveModelBridge
