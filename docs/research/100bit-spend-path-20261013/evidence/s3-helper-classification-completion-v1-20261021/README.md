# S3 grouped-helper classification completion packet

This packet assembles existing green, source-pinned Lean owners. It does not compile or alter their sources.

1. `AspisR1.S3OptimizedInactiveTableBridge.actual_s2_row_call_matches_optimized_table_cell` proves for every `j : Fin 64` and `s : Fin 16` that the actual extracted S2 `Variant::row(16*j+s)` followed by the actual inactive helper equals the optimized literal lookup bit. Its source checker pins optimized masks, group table, and dispatch to frozen Rust. This covers all 1024 cells.
2. `AspisR1GroupedPairActualFieldOpsV3.ActualGroupedPairSourceRow.actual_grouped_success_has_source_row_functional` proves that, assuming `CanonicalLow low` and success of the extracted grouped helper, its decoded output is the exact source-row ungrouped functional. The proof reuses the emitted 64-row coefficient loop, 16-step mask weighting, and 64×16 `s3_grouped_pair_exact` classification.

Together these close S3 lookup/classification and grouped-helper meaning at the extracted helper's successful-run contract. They do not prove `CanonicalLow` from the enclosing method, helper totality, or full `Weights::pair` source-order/effect refinement. Those remain in the S9 caller track. No production source was changed.
