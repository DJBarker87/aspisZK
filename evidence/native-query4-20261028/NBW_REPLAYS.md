# Exact NBO replay status

| Predecessor | Replay | Status | Native cut |
|---|---|---|---|
| NBO_K002 | NBW_K014 | PASS | `NBW_prefix_all_g` |
| NBO_K004 | NBW_K015 | PASS | `NBW_line_geometry_routing` |
| NBO_K005 | NBW_K016 | TIMEOUT | `NBW_capacity_raw_projection` |
| NBO_K006 | NBW_K017 | TIMEOUT | `NBW_capacity_weight_projection` |
| NBO_K007 | NBW_K018 | TIMEOUT | `NBW_capacity_line_projection` |
| NBO_K008 | NBW_K019 | TIMEOUT | `NBW_capacity_inverse_projection` |
| NBO_K009 | NBW_K020 | PASS | `NBW_tail_assignment` |
| NBO_K010 | NBW_K021 | PASS | `NBW_borrowed_push_frame` |
| NBO_K011 | NBW_K022 | PASS | `NBW_finish_one_store` |
| NBO_K012 | NBW_K023 | TIMEOUT | `NBW_actual_query_reject` |
| NBO_K015 | NBW_K024 | PASS | `NBW_full_proof_prefix` |
| NBO_K017 | NBW_K025 | PASS | `NBW_none_mark_native` |
| NBO_K019 | NBW_K026 | PASS | `NBW_return_carriers` |
| NBO_K020 | NBW_K027 | PASS | `NBW_node_dispatch_context` |
| NBO_K021 | NBW_K028 | TIMEOUT | `NBW_full_proof_actual_reject` |
| NBO_K023 | NBW_K029 | PASS | `NBW_wide_scalar_dispatch` |
| NBO_K024 | NBW_K030 | PASS | `NBW_basis_store_full_copy_bound` |
| NBO_K025 | NBW_K031 | PASS | `NBW_range_next_bounded` |
| NBO_K026 | NBW_K032 | PASS | `NBW_basis_initializer` |
| NBO_K027 | NBW_K033 | PASS | `NBW_basis_outer_after_inner` |
| NBO_K028 | NBW_K034 | TIMEOUT | `NBW_full_row_body` |
| NBO_K029 | NBW_K035 | PASS | `NBW_initializer_borrowed_step` |
| NBO_K031 | NBW_K036 | PASS | `NBW_coeff_common_h0` |
| NBO_K032 | NBW_K037 | PASS | `NBW_coeff_circle_h1` |
| NBO_K033 | NBW_K038 | PASS | `NBW_coeff_circle_h2` |
| NBO_K034 | NBW_K039 | PASS | `NBW_coeff_circle_h3` |
| NBO_K035 | NBW_K040 | PASS | `NBW_coeff_line_h2` |
| NBO_K036 | NBW_K041 | PASS | `NBW_coeff_line_c0` |
| NBO_K037 | NBW_K042 | PASS | `NBW_coeff_line_c1` |
| NBO_K038 | NBW_K043 | PASS | `NBW_coeff_line_h1` |
| NBO_K039 | NBW_K044 | PASS | `NBW_coeff_line_h3` |
| NBO_K040 | NBW_K045 | PASS | `NBW_horner_argument_cut` |

PASS restores only that inherited local property/domain under exact KMX configuration; it does not close its stubbed callees. TIMEOUT supplies no credit or counterexample. Prior unchanged timeout shapes were not replayed. NBB add/fold steps use K046/K047 with exact prefix rename and KMX attributes; their Lean value/trace results are imported unchanged.
