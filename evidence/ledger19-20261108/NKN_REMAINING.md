# NKN remaining obligations

Target not yet established.40/40 Lean/link/audit scopes;0Kani/0extraction. Eleven candidates admitted only after the full gate;46 occurrences remain OPEN. The original obligations and parent clauses remain in NKN_LEDGER.json.xz. This refresh has no Kani/extraction authority. Existing reviewed-cut substitution, domain/frame/induction/trace joins remain Lean-only work for the owning lanes; native gaps below require matched cuts/controls in those lanes, not an audit rerun.

## crates/aspis-core/src/circle.rs

| Row | Member | Remaining obligation | Live owner |
|---|---|---|---|
| TX1:NGB004 | secure_ood_circle_point_from_parameter | Complete circle-point source/native/cohort association including canonical parameter and branch domains. Missing native scalar/call windows and matched controls need Kani; field rule-A substitution/case split and domain transport are Lean-only. OPEN children: TX1:NGB006. | NKM_ circle-points |
| TX1:NGB006 | secure_circle_point_from_parameter | Complete circle-point source/native/cohort association including canonical parameter and branch domains. Missing native scalar/call windows and matched controls need Kani; field rule-A substitution/case split and domain transport are Lean-only. | NKM_ circle-points |

## crates/aspis-core/src/transcript.rs

| Row | Member | Remaining obligation | Live owner |
|---|---|---|---|
| TX1:NGB002 | circle_fallback_point | Complete circle-point source/native/cohort association including canonical parameter and branch domains. Missing native scalar/call windows and matched controls need Kani; field rule-A substitution/case split and domain transport are Lean-only. OPEN children: TX1:NGB004. | NKM_ circle-points |

## crates/aspis-r1-cost-probe/src/candidate.rs

| Row | Member | Remaining obligation | Live owner |
|---|---|---|---|
| TX1:081 | batch_merkle | Propagate exact batch_tree returned errors at SAME ? sites, ordered prefix and no suffix; child tree OPEN. Native source segment/call-site controls where absent require Kani; child-domain/Result/effect composition is Lean-only. OPEN children: TX1:082. | NKL_ batch-merkle3 |
| TX1:082 | batch_merkle_values | Propagate exact batch_tree returned errors at SAME ? sites, ordered prefix and no suffix; child tree OPEN. Native source segment/call-site controls where absent require Kani; child-domain/Result/effect composition is Lean-only. OPEN children: TX1:083. | NKL_ batch-merkle3 |
| TX1:083 | batch_tree | NKB-F1: exact returned Err(Parse)/Err(Merkle) versus reused pending-none/fail. Need explicit frozen Result segment cuts/control plus same ordered-prefix rejection transport to adopted model (bb)(1)-(2). Native new cuts require Kani; transport/frame/propagation is Lean-only. TX2 uses <=12 indices/9216-byte entry, superseded10-leaf clause retained. | NKL_ batch-merkle3 |
| TX1:084 | canonical_scan | Compose SAME canonical scan over CLOSED189 echeck, exact parser/loop frame and error prefixes. Missing native parent cut/control needs Kani; child instantiation and finite induction are Lean-only. | NKL_ batch-merkle3 |
| TX1:087 | prepare | Complete SAME-function native/source/full Result/abort/post/frame/ordered-effects packet remains unadmitted. Missing native one-step/call-site cuts/control need Kani; existing-cut substitution/canonical unit domains/frame/induction/cohort joins are Lean-only. OPEN children: TX1:137. | UNOWNED in current brief; lead routing required |
| TX1:094 | tx1 | Complete SAME-function native/source/full Result/abort/post/frame/ordered-effects packet remains unadmitted. Missing native one-step/call-site cuts/control need Kani; existing-cut substitution/canonical unit domains/frame/induction/cohort joins are Lean-only. OPEN children: TX1:081, TX1:084, TX1:087. | UNOWNED in current brief; lead routing required |
| TX2:053 | batch_merkle | Propagate exact batch_tree returned errors at SAME ? sites, ordered prefix and no suffix; child tree OPEN. Native source segment/call-site controls where absent require Kani; child-domain/Result/effect composition is Lean-only. OPEN children: TX2:054. | NKL_ batch-merkle3 |
| TX2:054 | batch_merkle_values | Propagate exact batch_tree returned errors at SAME ? sites, ordered prefix and no suffix; child tree OPEN. Native source segment/call-site controls where absent require Kani; child-domain/Result/effect composition is Lean-only. OPEN children: TX2:055. | NKL_ batch-merkle3 |
| TX2:055 | batch_tree | NKB-F1: exact returned Err(Parse)/Err(Merkle) versus reused pending-none/fail. Need explicit frozen Result segment cuts/control plus same ordered-prefix rejection transport to adopted model (bb)(1)-(2). Native new cuts require Kani; transport/frame/propagation is Lean-only. TX2 uses <=12 indices/9216-byte entry, superseded10-leaf clause retained. | NKL_ batch-merkle3 |
| TX2:064 | tx2_authenticated | Complete SAME-function native/source/full Result/abort/post/frame/ordered-effects packet remains unadmitted. Missing native one-step/call-site cuts/control need Kani; existing-cut substitution/canonical unit domains/frame/induction/cohort joins are Lean-only. OPEN children: TX2:065. | UNOWNED in current brief; lead routing required |
| TX2:065 | tx2_common | M01 SAME resume/query/flush/finish parent invocation/log assembly. Generalized current-word115 supplement remains CLOSED outside599; batch M02 remains OPEN. Missing native parent cuts/control need Kani; child/domain/source-prefix composition is Lean-only. OPEN children: TX2:053, TX2:124. | NKE_ tx2-native9 (M01 join) |

## crates/aspis-r1-cost-probe/src/r1_semantic.rs

| Row | Member | Remaining obligation | Live owner |
|---|---|---|---|
| TX1:136 | verify_finish | SAME terminal caller/child arguments, all Result/effects and native packet assembly. Use admitted NKJ040/041/043 at225 with canonical arrays/arity/budget, and NKG308 at actual evaluator call. Native missing segments/control need Kani; child-domain/loop/frame/source assembly is Lean-only. OPEN children: TX1:256. | NKI_ terminal4 (256 and terminal parents, including225) |
| TX1:137 | verify_observed | Complete SAME-function native/source/full Result/abort/post/frame/ordered-effects packet remains unadmitted. Missing native one-step/call-site cuts/control need Kani; existing-cut substitution/canonical unit domains/frame/induction/cohort joins are Lean-only. OPEN children: TX1:136. | UNOWNED in current brief; lead routing required |

## crates/aspis-r1-cost-probe/src/verifier.rs

| Row | Member | Remaining obligation | Live owner |
|---|---|---|---|
| TX2:124 | resume | Complete resume native log/cursor/owned-carrier/cleanup assembly at SAME original bytes and all errors. Missing native windows/control need Kani; CLOSED Reader/header/parser/domain/effect substitutions and allocator assembly are Lean-only. | NKK_ tx2-resume |

## crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs

| Row | Member | Remaining obligation | Live owner |
|---|---|---|---|
| TX1:218 | evaluate_with_selectors | SAME terminal caller/child arguments, all Result/effects and native packet assembly. Use admitted NKJ040/041/043 at225 with canonical arrays/arity/budget, and NKG308 at actual evaluator call. Native missing segments/control need Kani; child-domain/loop/frame/source assembly is Lean-only. OPEN children: TX1:220. | NKI_ terminal4 (256 and terminal parents, including225) |
| TX1:220 | finish_selector_tensor_basis | SAME terminal caller/child arguments, all Result/effects and native packet assembly. Use admitted NKJ040/041/043 at225 with canonical arrays/arity/budget, and NKG308 at actual evaluator call. Native missing segments/control need Kani; child-domain/loop/frame/source assembly is Lean-only. OPEN children: TX1:225. | NKI_ terminal4 (256 and terminal parents, including225) |
| TX1:225 | qm31_sum_products_up_to4 | SAME terminal caller/child arguments, all Result/effects and native packet assembly. Use admitted NKJ040/041/043 at225 with canonical arrays/arity/budget, and NKG308 at actual evaluator call. Native missing segments/control need Kani; child-domain/loop/frame/source assembly is Lean-only. | NKI_ terminal4 (256 and terminal parents, including225) |

## crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs

| Row | Member | Remaining obligation | Live owner |
|---|---|---|---|
| TX1:232 | add_schedule_lanes | SAME terminal caller/child arguments, all Result/effects and native packet assembly. Use admitted NKJ040/041/043 at225 with canonical arrays/arity/budget, and NKG308 at actual evaluator call. Native missing segments/control need Kani; child-domain/loop/frame/source assembly is Lean-only. OPEN children: TX1:260. | NKI_ terminal4 (256 and terminal parents, including225) |
| TX1:233 | add_value_lanes | SAME terminal caller/child arguments, all Result/effects and native packet assembly. Use admitted NKJ040/041/043 at225 with canonical arrays/arity/budget, and NKG308 at actual evaluator call. Native missing segments/control need Kani; child-domain/loop/frame/source assembly is Lean-only. | NKI_ terminal4 (256 and terminal parents, including225) |
| TX1:234 | append_level_packed_selector_tensor | SAME terminal caller/child arguments, all Result/effects and native packet assembly. Use admitted NKJ040/041/043 at225 with canonical arrays/arity/budget, and NKG308 at actual evaluator call. Native missing segments/control need Kani; child-domain/loop/frame/source assembly is Lean-only. | NKI_ terminal4 (256 and terminal parents, including225) |
| TX1:235 | append_levels_packed_selector_tensor | SAME terminal caller/child arguments, all Result/effects and native packet assembly. Use admitted NKJ040/041/043 at225 with canonical arrays/arity/budget, and NKG308 at actual evaluator call. Native missing segments/control need Kani; child-domain/loop/frame/source assembly is Lean-only. OPEN children: TX1:234. | NKI_ terminal4 (256 and terminal parents, including225) |
| TX1:237 | composition_parts | SAME terminal caller/child arguments, all Result/effects and native packet assembly. Use admitted NKJ040/041/043 at225 with canonical arrays/arity/budget, and NKG308 at actual evaluator call. Native missing segments/control need Kani; child-domain/loop/frame/source assembly is Lean-only. OPEN children: TX1:218, TX1:261. | NKI_ terminal4 (256 and terminal parents, including225) |
| TX1:250 | public_digest_packed | SAME terminal caller/child arguments, all Result/effects and native packet assembly. Use admitted NKJ040/041/043 at225 with canonical arrays/arity/budget, and NKG308 at actual evaluator call. Native missing segments/control need Kani; child-domain/loop/frame/source assembly is Lean-only. OPEN children: TX1:251. | NKI_ terminal4 (256 and terminal parents, including225) |
| TX1:251 | public_digest_packed_selector_tensor | SAME terminal caller/child arguments, all Result/effects and native packet assembly. Use admitted NKJ040/041/043 at225 with canonical arrays/arity/budget, and NKG308 at actual evaluator call. Native missing segments/control need Kani; child-domain/loop/frame/source assembly is Lean-only. OPEN children: TX1:235. | NKI_ terminal4 (256 and terminal parents, including225) |
| TX1:256 | r0::Public<'a>::terminal_qm31 | SAME terminal caller/child arguments, all Result/effects and native packet assembly. Use admitted NKJ040/041/043 at225 with canonical arrays/arity/budget, and NKG308 at actual evaluator call. Native missing segments/control need Kani; child-domain/loop/frame/source assembly is Lean-only. OPEN children: TX1:263. | NKI_ terminal4 (256 and terminal parents, including225) |
| TX1:260 | semantic_initial_and_absorption | SAME terminal caller/child arguments, all Result/effects and native packet assembly. Use admitted NKJ040/041/043 at225 with canonical arrays/arity/budget, and NKG308 at actual evaluator call. Native missing segments/control need Kani; child-domain/loop/frame/source assembly is Lean-only. | NKI_ terminal4 (256 and terminal parents, including225) |
| TX1:261 | semantic_packed | SAME terminal caller/child arguments, all Result/effects and native packet assembly. Use admitted NKJ040/041/043 at225 with canonical arrays/arity/budget, and NKG308 at actual evaluator call. Native missing segments/control need Kani; child-domain/loop/frame/source assembly is Lean-only. OPEN children: TX1:232, TX1:233, TX1:250. | NKI_ terminal4 (256 and terminal parents, including225) |
| TX1:263 | terminal_parts | SAME terminal caller/child arguments, all Result/effects and native packet assembly. Use admitted NKJ040/041/043 at225 with canonical arrays/arity/budget, and NKG308 at actual evaluator call. Native missing segments/control need Kani; child-domain/loop/frame/source assembly is Lean-only. OPEN children: TX1:237. | NKI_ terminal4 (256 and terminal parents, including225) |

## programs/r1-cost-probe/src/lib.rs

| Row | Member | Remaining obligation | Live owner |
|---|---|---|---|
| TX1:328 | first_decoded | Actual entry/adapter account/input/op association, full Result/error/borrow/drop/ordered effects and native frames. Missing native prefix/carrier/control needs Kani or pinned SDK law; CLOSED child domains and source/continuation joins are Lean-only. Driver OPEN children block entry. OPEN children: TX1:094. | UNOWNED in current brief; lead routing required |
| TX1:330 | process_r1_cost_probe_instruction | Actual entry/adapter account/input/op association, full Result/error/borrow/drop/ordered effects and native frames. Missing native prefix/carrier/control needs Kani or pinned SDK law; CLOSED child domains and source/continuation joins are Lean-only. Driver OPEN children block entry. OPEN children: TX1:333. | UNOWNED in current brief; lead routing required |
| TX2:213 | process_r1_cost_probe_instruction | Actual entry/adapter account/input/op association, full Result/error/borrow/drop/ordered effects and native frames. Missing native prefix/carrier/control needs Kani or pinned SDK law; CLOSED child domains and source/continuation joins are Lean-only. Driver OPEN children block entry. OPEN children: TX2:221. | UNOWNED in current brief; lead routing required |

## programs/r1-cost-probe/src/r1_pool_adapter.rs

| Row | Member | Remaining obligation | Live owner |
|---|---|---|---|
| TX1:333 | process | Actual entry/adapter account/input/op association, full Result/error/borrow/drop/ordered effects and native frames. Missing native prefix/carrier/control needs Kani or pinned SDK law; CLOSED child domains and source/continuation joins are Lean-only. Driver OPEN children block entry. OPEN children: TX1:344. | UNOWNED in current brief; lead routing required |
| TX2:216 | decode_checkpoint_box | Actual entry/adapter account/input/op association, full Result/error/borrow/drop/ordered effects and native frames. Missing native prefix/carrier/control needs Kani or pinned SDK law; CLOSED child domains and source/continuation joins are Lean-only. Driver OPEN children block entry. | UNOWNED in current brief; lead routing required |
| TX2:217 | decode_lane_from_pool_release | Actual entry/adapter account/input/op association, full Result/error/borrow/drop/ordered effects and native frames. Missing native prefix/carrier/control needs Kani or pinned SDK law; CLOSED child domains and source/continuation joins are Lean-only. Driver OPEN children block entry. | UNOWNED in current brief; lead routing required |
| TX2:218 | decode_master_box | Actual entry/adapter account/input/op association, full Result/error/borrow/drop/ordered effects and native frames. Missing native prefix/carrier/control needs Kani or pinned SDK law; CLOSED child domains and source/continuation joins are Lean-only. Driver OPEN children block entry. | UNOWNED in current brief; lead routing required |
| TX2:221 | process | Actual entry/adapter account/input/op association, full Result/error/borrow/drop/ordered effects and native frames. Missing native prefix/carrier/control needs Kani or pinned SDK law; CLOSED child domains and source/continuation joins are Lean-only. Driver OPEN children block entry. OPEN children: TX2:240. | UNOWNED in current brief; lead routing required |

## programs/r1-cost-probe/src/r1_pool_adapter_owned.rs

| Row | Member | Remaining obligation | Live owner |
|---|---|---|---|
| TX1:344 | stage1 | Actual entry/adapter account/input/op association, full Result/error/borrow/drop/ordered effects and native frames. Missing native prefix/carrier/control needs Kani or pinned SDK law; CLOSED child domains and source/continuation joins are Lean-only. Driver OPEN children block entry. OPEN children: TX1:345. | UNOWNED in current brief; lead routing required |
| TX1:345 | stage1_owned | Actual entry/adapter account/input/op association, full Result/error/borrow/drop/ordered effects and native frames. Missing native prefix/carrier/control needs Kani or pinned SDK law; CLOSED child domains and source/continuation joins are Lean-only. Driver OPEN children block entry. OPEN children: TX1:328. | UNOWNED in current brief; lead routing required |
| TX2:233 | authenticate_asq8_accounts | Actual entry/adapter account/input/op association, full Result/error/borrow/drop/ordered effects and native frames. Missing native prefix/carrier/control needs Kani or pinned SDK law; CLOSED child domains and source/continuation joins are Lean-only. Driver OPEN children block entry. OPEN children: TX2:216, TX2:217, TX2:218, TX2:234. | UNOWNED in current brief; lead routing required |
| TX2:234 | authenticate_invariant_release_registry | Actual entry/adapter account/input/op association, full Result/error/borrow/drop/ordered effects and native frames. Missing native prefix/carrier/control needs Kani or pinned SDK law; CLOSED child domains and source/continuation joins are Lean-only. Driver OPEN children block entry. | UNOWNED in current brief; lead routing required |
| TX2:240 | stage2 | Actual entry/adapter account/input/op association, full Result/error/borrow/drop/ordered effects and native frames. Missing native prefix/carrier/control needs Kani or pinned SDK law; CLOSED child domains and source/continuation joins are Lean-only. Driver OPEN children block entry. OPEN children: TX2:241. | UNOWNED in current brief; lead routing required |
| TX2:241 | stage2_owned | Actual entry/adapter account/input/op association, full Result/error/borrow/drop/ordered effects and native frames. Missing native prefix/carrier/control needs Kani or pinned SDK law; CLOSED child domains and source/continuation joins are Lean-only. Driver OPEN children block entry. OPEN children: TX2:064, TX2:242. | UNOWNED in current brief; lead routing required |
| TX2:242 | validate_asq8 | Actual entry/adapter account/input/op association, full Result/error/borrow/drop/ordered effects and native frames. Missing native prefix/carrier/control needs Kani or pinned SDK law; CLOSED child domains and source/continuation joins are Lean-only. Driver OPEN children block entry. OPEN children: TX2:233. | UNOWNED in current brief; lead routing required |

## Separate obligations

All named Pool obligations in NKN_PHYSICAL.md remain OPEN/conditional as named; no finite complete production inventory is claimed. NJY-B1 Box/ProgramError wrappers48/49 remain OPEN. Entry/op9/native parent/Pool continuation, L187 cold replay and L188 artifact/extraction joins remain. K086 and owner(aj)(a) remain unresolved. Retained off-domain115 supplement is CLOSED; no new parent credit.
