# Failing and blocked steps

| Stage/attempt | Exact assertion or missing law | Classification / replacement |
|---|---|---|
| S3 K004, K013 | Whole flat proof backing with decoder arithmetic | Tool timeout; excluded; split original backing into contiguous repr(C) segments, each fully arbitrary |
| S3 K015, K016 | Parent limit before full-law flat/fixed-limb/byte shape completed | Tool parent180s; excluded; segmented backing and smaller scalar association; no timeout/cap increase |
| S3 K017 | Direct internal write_any shape reached unsupported unwinding | Tool/fixture failure; excluded; ordinary kani::any fixed fields instead |
| S3 K024 | Bad decoded reply hits runtime-formatted assert_eq placeholder | Diagnostic excluded; K025/K026 use explicit assertion, one failing check pinned to source line50 |
| S1 K027, K028 | Physical post-write projection of full expansion output | Tool90s timeout; excluded; logging effect window plus CLOSED complete callee law and Lean back-functions |
| S1 K029 | Dense scalar source read/log backing | Parent180s; excluded; segmented arbitrary proof representation and one exact typed-field source-byte read/address |
| E001 / step3 | Charon succeeds; Aeneas Not_found at InterpReduceCollapse.ml1991 after constructor remained Transparent | OWN INPUT BOUNDARY: opacity pattern missed inherent Prepared::new impl. Not evidence prepare is unextractable. One extraction budget consumed; no usable emitted prepare output. Pins and declaration/span diagnosis retained; no rerun |
| S4 | verify_observed TX1:137 full native/model Result/scratch packet | Missing callee law, sibling-owned; NHG handoff at307d36e829c remains OPEN. No assertion is assumed |
| S5 | Prepared::new TX1:179 complete sampler/query/native producer-to-final-record packet | Missing callee law, NGN_FAILING_STEP; no assertion is assumed |
| Parent composition | Six-stage emitted frozen body with the SAME full callee records and failures | Missing E001 output and S4/S5 packets; TX1:087 stays OPEN |

K014 was refused by the serial guard before launch; L015 and L045 were refused during dependency pinning before launch. Charged conservatively; no extra scopes. L045 was resolved by citing the existing filled_exact theorem directly (the entire NGC wrapper), without rebuilding unchanged objects. Failed focused Lean parser/tactic attempts remain in receipts and are not selected.

The first local validator failed because the older unchanged NFK admission loop expects caller_domain_obligations on12 newer OPEN NGB inventory rows. NHF's adapter inserts an explicit OPEN unresolved-schema barrier for those rows during the unchanged loop, verifies they stay OPEN, and restores the original rows byte-for-byte. It does not discard dependencies or alter admission predicates. Ten mutation denials exercise the added gates. No source, toolchain, cap, timeout, historical denial, trust row or security contract is relaxed.
