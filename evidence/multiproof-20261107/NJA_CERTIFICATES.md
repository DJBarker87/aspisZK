# NJA certificates — in progress

No composed row has been admitted. All 28 occurrences remain OPEN until the combined gate and next ledger review. Extraction pins are in NJA_emitted/NHR_PINS.json; exact declaration split hashes in NJA_SPLIT.json. Only NJA_Multiproof.Types, NJA_Small, NJA_Arity and NJA_Reads have successful focused compiles so far. The full Funs adaptation FAILED and is excluded; its sorryAx diagnostic is not accepted evidence.

| Source helper | Native positive | Matched control | Lean support | Current limit |
|---|---|---|---|---|
| Arity::bits | K009 | K002 FAIL | NJA_Arity.two_bits/eight_bits, L007 | cohort caller association pending |
| Arity::width | K003 | K004 FAIL | NJA_Arity.two_width/eight_width, L007 | cohort checked-shift association pending |
| Arity::levels | K005 | K006 FAIL | NJA_Arity.two_levels/eight_levels, L007 | cohort association pending |
| index_at | K007 | K008 FAIL | NJA_Arity.index_result, NJA_Reads.index_ok/index_bad, L007/L008 | SAME caller array/index association pending |

All native positives/control pairs use actual frozen bodies and no writable static, function-pointer observation, field product or copy-dependent assertion. Every run validates the frozen dependency graph offline and checks the unchanged lock afterward. Native bodies are modified only by appending NJA cfg(kani) harnesses in scratch, retained as exact per-attempt patches. K001 is an excluded compile failure on a missing frozen cfg(kani) input; K009 repairs the input set with Git/SHA pins, not a timed-out-shape retry. No LPb credit is reused.

Retain P6/D188 option-A source/extraction/native semantic transport and existing std/allocator/runtime/source-to-ELF qualifications. This is reclassification, not premise removal. No new runtime trust row or security metric.

L011 additionally proves NJA_CohortArity.bits/width/levels/index/value against the ACTUAL retained AspisR1Stage2 emitted helper bodies from R22Stage2LocalBodies, with explicit arity transport. Width includes checked-versus-wrapping shift equality on both constructors. Standard axioms only. The value equation is a source/model support fact, NOT resolution of the eight-way-only inventory/caller finding. Parents and count splits remain under development; failed L012/L013 are excluded.

K010/K011 certify root_matches and its inverted-result control. K012..K019 cover empty/oversized well_formed and node_count rejection, with matched controls; only those rejection classes, no accepted-buffer claim. Iterator/prestate and invalid verify entry stages are configured next.
