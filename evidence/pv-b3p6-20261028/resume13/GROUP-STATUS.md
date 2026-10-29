# D467 exact link status

Coverage: 79 conservative candidates / 39 BOUND = 39 reclassification + 0 fully composed own-1. Runjoin op227 remains undischarged. The complete requested all-group skeleton remains incomplete.

| Missing-model body | Exact statement / compiled law | Status |
|---|---|---|
| private_public | ScalarBinding13227.PV_B3P_Link_private_public | Exact-span extraction BOUND by b3p6-1; carrier law compiled |
| withdrawal_public | ScalarBinding13227.PV_B3P_Link_withdrawal_public | Exact-span extraction BOUND by b3p6-1; carrier law compiled |
| semantic | TopDown13227.PV_B3P_Link_semantic; ScalarBinding13227.semantic_source_binding13 | Exact-span extraction BOUND by b3p6-1; emitted match consumed |
| transition | Binding13227.PV_B3P_Link_transition | Two-arm model law compiled; exact native/reference-return association OPEN |
| fields | Binding13227.PV_B3P_Link_fields | Typed Prop and partial-write/error model compiled; native Vec association OPEN |
| frontier | Binding13227.PV_B3P_Link_frontier | Typed Prop and short-circuit model compiled; exact twenty native calls/Vec association OPEN |
| terminal_qm31 | TopDown13227.PV_B3P_Link_terminal_qm31 | Explicit wrapper equation, OPEN for native ops |

Namespaces above have the `PV_B3P_` prefix. Exact definitions are in the retained Lean sources; these are not axioms. fields carries an allocation-sensitive append port and retains partial output on Rust Err.

| Function | Unchanged named Link | Model-instance status | Direct native association |
|---|---|---|---|
| absorption_lanes_literal | `PV_B3P_Link_terminal_absorption_lanes_literal` | OPEN / no source-model instance | OPEN: no complete native/dependency association credited |
| add_digest_binding | `PV_B3P_Link_terminal_add_digest_binding` | `digeststore_link13` | OPEN: no complete native/dependency association credited |
| add_path_lanes | `PV_B3P_Link_terminal_add_path_lanes` | OPEN / no source-model instance | OPEN: no complete native/dependency association credited |
| add_preweighted | `PV_B3P_Link_terminal_add_preweighted` | `preweighted_link13` | OPEN: no complete native/dependency association credited |
| add_schedule_lanes | `PV_B3P_Link_terminal_add_schedule_lanes` | OPEN / no source-model instance | OPEN: no complete native/dependency association credited |
| add_value_lanes | `PV_B3P_Link_terminal_add_value_lanes` | `value_link13` | OPEN: no complete native/dependency association credited |
| composition_parts | `PV_B3P_Link_terminal_composition_parts` | OPEN / no source-model instance | OPEN: no complete native/dependency association credited |
| equality_value | `PV_B3P_Link_terminal_equality_value` | `equality_link13` | OPEN: no complete native/dependency association credited |
| occupancy_lanes_literal | `PV_B3P_Link_terminal_occupancy_lanes_literal` | OPEN / no source-model instance | OPEN: no complete native/dependency association credited |
| path_lanes_literal | `PV_B3P_Link_terminal_path_lanes_literal` | OPEN / no source-model instance | OPEN: no complete native/dependency association credited |
| poseidon_selectors | `PV_B3P_Link_terminal_poseidon_selectors` | OPEN / no source-model instance | OPEN: no complete native/dependency association credited |
| public_digest_lanes | `PV_B3P_Link_terminal_public_digest_lanes` | `digest_link13` | OPEN: no complete native/dependency association credited |
| reconstruct_10 | `PV_B3P_Link_terminal_reconstruct_10` | `reconstruct_link13` | OPEN: no complete native/dependency association credited |
| semantic_initial_and_absorption | `PV_B3P_Link_terminal_semantic_initial_and_absorption` | OPEN / no source-model instance | OPEN: no complete native/dependency association credited |
| semantic_packed | `PV_B3P_Link_terminal_semantic_packed` | OPEN / no source-model instance | OPEN: no complete native/dependency association credited |
| sum_high | `PV_B3P_Link_terminal_sum_high` | `sum_high_link13` | OPEN: no complete native/dependency association credited |
| validate_transition | `PV_B3P_Link_terminal_validate_transition` | OPEN / no source-model instance | OPEN: no complete native/dependency association credited |
| active_literal | `PV_B3P_Link_copy_active_literal` | `active_adapter_link13` | OPEN: no complete native/dependency association credited |
| pattern_values_literal | `PV_B3P_Link_copy_pattern_values_literal` | `pattern_link13` | OPEN: no complete native/dependency association credited |
| selector_mask_sum_16 | `PV_B3P_Link_copy_selector_mask_sum_16` | `frozen_mask_adapter_link13` | REFUTED at mask=0; actual frozen caller domain and contextual adapter proved; Link definition unchanged |
| qm31_m31_dot | `PV_B3P_Link_field_qm31_m31_dot` | OPEN / no source-model instance | OPEN: no complete native/dependency association credited |
| qm31_sum_products3_prepared | `PV_B3P_Link_field_qm31_sum_products3_prepared` | `PV_B3P_Binding13227.prepared_link13` | OPEN: no complete native/dependency association credited |
| at_point | `PV_B3P_Link_poseidon_at_point` | OPEN / no source-model instance | REFUTED for legacy 49-block constructor at Boolean coordinate 50; unchanged target has 57 blocks; no deployed op227 counterexample claimed |
| evaluate_state_only_poseidon_oracle_projected | `PV_B3P_Link_poseidon_evaluate_state_only_poseidon_oracle_projected` | `projected_link13` | OPEN: no complete native/dependency association credited |
| expand | `PV_B3P_Link_poseidon_expand` | OPEN / no source-model instance | OPEN: no complete native/dependency association credited |
| external_linear_lazy | `PV_B3P_Link_poseidon_external_linear_lazy` | OPEN / no source-model instance | OPEN: no complete native/dependency association credited |
| external_linear_packed | `PV_B3P_Link_poseidon_external_linear_packed` | OPEN / no source-model instance | OPEN: no complete native/dependency association credited |
| external_local_packed_raw | `PV_B3P_Link_poseidon_external_local_packed_raw` | OPEN / no source-model instance | OPEN: no complete native/dependency association credited |
| full_round | `PV_B3P_Link_poseidon_full_round` | `round_link13_QPlain` | OPEN: no complete native/dependency association credited |
| full_round_m31_constants | `PV_B3P_Link_poseidon_full_round_m31_constants` | `round_link13_MPlain` | OPEN: no complete native/dependency association credited |
| full_round_m31_constants_packed | `PV_B3P_Link_poseidon_full_round_m31_constants_packed` | `round_link13_MPacked` | OPEN: no complete native/dependency association credited |
| full_round_packed | `PV_B3P_Link_poseidon_full_round_packed` | `round_link13_QPacked` | OPEN: no complete native/dependency association credited |
| internal_linear_lazy | `PV_B3P_Link_poseidon_internal_linear_lazy` | `internal_link13` | OPEN: no complete native/dependency association credited |
| interpolate_three_constant_columns | `PV_B3P_Link_poseidon_interpolate_three_constant_columns` | OPEN / no source-model instance | OPEN: no complete native/dependency association credited |
| interpolated_internal_pair | `PV_B3P_Link_poseidon_interpolated_internal_pair` | OPEN / no source-model instance | OPEN: no complete native/dependency association credited |
| leading_pair_packed | `PV_B3P_Link_poseidon_leading_pair_packed` | `leading_link13` | OPEN: no complete native/dependency association credited |

18 of 36 model/context-adapter instances are discharged. Their native source interpretation is not inferred from the group model witness. The 49-block selector and zero-mask counterexamples are documented in FINDINGS.md; no Link was weakened.

| Other group | Status |
|---|---|
| D188 | Four owned emission families / sixteen finite comparisons pass; matching perturbation fails. Full actual-source/caller restoration closure OPEN. No complete standalone D188 group was connected to the skeleton. |
| Matrix | 270 instrumented snapshots / 2430 entries and ten final deployed Results match; negative store control fails. Actual internal-state/type-adapter binding OPEN; generic MatrixStore proof rejected, MatrixTrace unsubmitted. No complete matrix group connected. |
| Slice | Four-slot forward non-ZST iteration, all restorations and actual group bounds compile. Native pointer/borrow constructor association OPEN. |
| Std/dependencies | Three deployed/extractor std bodies token-identical; source dossier and Range laws retained. Complete pre-inline source-cone binding OPEN. No complete std coverage group connected. |

The first-15 requirement was met only for exact conclusion text (ordinal 14), not for the complete requested group decomposition. All reported skeletons have explicit joint model witnesses; none is credited as native closure.
