# NKK certificates

TX2:124 OPEN; target not yet established. These are native segment candidates, not composed-row credit.

| Native source segment | PASS | Matched failing controls | Scope |
|---|---|---|---|
| query_chunk8 | K003 | K004 reply inversion | 8 raw4 calls, arbitrary incoming Reader/replies/posts, exact full array/cursor/immutable backing log |
| query_chunk6 | K006 | K007 reply / K008 incoming cursor assertion | final6 raw4 calls, same interface |
| state_roots_stage | K009 | K010 reply / K011 incoming cursor assertion | source state/root raw32 triple, all bytes and complete log |
| gamma_stage | K013 | K014 result / K015 incoming cursor assertion | 4 E and1 K full replies; every exact error and prefix; E oracle values include constructor normalization |
| z_claim_stage | K016 | K017 result / K018 incoming cursor assertion | 4 K,2 E,1 K; full outputs and every error prefix |
| semantic_writeback_stage | K019 | K020 result; K021 wrong-cursor control invalid (PASS) | SAME bytes/cursor, full array10/cursor reply and following K call; F2 repair pending |

Attempt IDs above are NKK_ prefixed. Exact source versions and caps/resource fields are retained in each receipt. Every Kani run validates the frozen dependency graph/deployed features with offline resolution and checks the lock hash unchanged afterwards. Positive and negative source versions remain pinned even as independent later segments are added. KMX patch bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67 is unchanged.

K001/K002 were own-input compilation failures, repaired without changing validation. K012 is the incorrect raw E expectation described in NKK_FINDINGS. K021 is the cancelled worker control described in F2. No Option<fn>-dependent or writable-static credits. No field multiplication proof, new trust row, extraction or release build.

Lean source clause support: L002 focused retained-root statements; L004 generic clause composition; L005 all9 event clauses; L008 finish-tail clauses; L009 query-end clauses. L010 heartbeat-limit shape retired; explicit literal-tail replacement in progress. Only successful receipts with standard #print axioms are selected. Failed diagnostics containing sorryAx are never accepted roots.

## Native allowance complete

50/50 Kani attempts terminal. NKK_NATIVE_CERTIFICATES.json is the authoritative12 positive segment pairs with their exact resource/source/graph/lock receipts. Added: owned_tail K022/023/024; repaired semantic K025/026/027; header K028/029/030; proof-digest modifies contract K042/046/047 plus supplementary wrong-argument K050; public0..1880 K034/035; checkpoint entire-prefix1736 K036/043/044; returned-pair ownership K045/048/049. K032/037--041 calibrate the borrowed-slice/Result<Unit,Error> contract shape before K042. K031's90s byte-selection timeout is retired; the changed modifies-instrumented shape protects the entire proof with a checked write set. Native transport uses the existing option-A P6/D188 trust classification.

The returned-pair ownership window asserts weights/rhs/power/next and Prepared.variant; it does not assert every Prepared scalar/array at the final return. Earlier NJJ_Prepared constructor cuts may not be promoted to that complete post-return frame without a SAME-argument frame chain. That assembly remains open. No row credit is claimed for12 passing segments or the source clause theorem.
