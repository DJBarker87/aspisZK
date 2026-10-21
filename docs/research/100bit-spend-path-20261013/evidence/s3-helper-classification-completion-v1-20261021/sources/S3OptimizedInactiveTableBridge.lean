import S3VariantInactiveComposition

set_option autoImplicit false
namespace AspisR1.S3OptimizedInactiveTableBridge

open Aeneas Aeneas.Std Result WP

/-- The actual optimized helper tests `S2_INACTIVE_MASKS[group] & (1 << bit)`.
This definition records that table-cell predicate over the exact literals
reused by `S3S9CurrentSourceModel`; `source-check.py` checks those literals and
the dispatch sites against the frozen Rust source. -/
def optimizedS2TableBit (j : Fin 64) (s : Fin 16) : Bool :=
  decide ((AspisR1.S3S9CurrentSourceModel.inactiveMasks.getD
    (AspisR1.S3S9CurrentSourceModel.inactiveGroups.getD j.val 0) 0) &&&
      2 ^ s.val != 0)

theorem optimized_s2_table_bit_is_group_bit (j : Fin 64) (s : Fin 16) :
    optimizedS2TableBit j s =
      AspisR1.S3S9CurrentSourceModel.inactiveAtGroup
        (AspisR1.S3S9CurrentSourceModel.groupAt j) s := by
  fin_cases j <;> fin_cases s <;> decide

theorem optimized_s2_table_bit_matches_row_inactive (j : Fin 64) (s : Fin 16) :
    optimizedS2TableBit j s =
      decide (AspisR1.S3S9CurrentSourceModel.sourceInactive
        (AspisR1.S3S9CurrentSourceModel.s2Row (16 * j.val + s.val)) = 1) := by
  rw [optimized_s2_table_bit_is_group_bit]
  exact (AspisR1.S3S9CurrentSourceModel.s3_group_classification j s).symm

theorem actual_s2_row_call_matches_optimized_table_cell (j : Fin 64) (s : Fin 16) :
    ∃ out,
      AspisR1.S3VariantRowAeneasCut.s2_row_result
        (AspisR1.S3VariantInactiveComposition.s2RowInput j s) = .ok out ∧
      out.val = AspisR1.S3S9CurrentSourceModel.s2Row (16 * j.val + s.val) ∧
      AspisR1S3InactiveSource.r0.opening.inactive out =
        .ok (core.result.Result.Ok (optimizedS2TableBit j s)) := by
  obtain ⟨out, hrun, hrow, hinactive⟩ :=
    AspisR1.S3VariantInactiveComposition.s2_variant_row_inactive_grouped j s
  refine ⟨out, hrun, hrow, ?_⟩
  rw [optimized_s2_table_bit_is_group_bit]
  exact hinactive

#print axioms optimized_s2_table_bit_is_group_bit
#print axioms optimized_s2_table_bit_matches_row_inactive
#print axioms actual_s2_row_call_matches_optimized_table_cell
end AspisR1.S3OptimizedInactiveTableBridge
