# NKU findings and replacements

Target not yet established; ledger credit waits for the next gate.

- L057: whole semantic source factorization reached the default200000 heartbeat limit. Retired. Split into NKU_TailSource (L063), NKU_FinishFactor (L064), NKU_FinishTransport (L066), then small source/state joins. No heartbeat/recursion/cap/timeout increase.
- L078:22-word query join reached the default heartbeat limit. Retired. Replaced by6/8/8 source-window joins (L083/L092/L093) and the small composition alias L094. No whole-vector replay.
- L145: broad generic success proof for the header end invariant terminated with lean::memory_exception, exit134,150.621s, reported process RSS10543664KiB, swap0; verified cgroup memory.high6442450944/max8589934592/swap0/tasks64, cgroup memory peak5008457728 bytes. This was reviewed immediately. No unchanged rerun or raised limit. The replacement explicitly splits prefix, one-any tail and final consumption (L149/L150/L151); all pass. The full G roots remained unchanged and green throughout.
- L138: constructor carrier mismatch (NID emitted versus Stage2 cohort). Excluded; no coercion assumed. NKU_SourceConstructors (L143) transcribes the existing complete native assertions on the actual emitted type. NKU_TerminalCut (L142) is explicitly cohort-side. See NKU_TERMINAL_CARRIER_REVIEW.md.
- Other failed attempts are ordinary syntax, missing-import or elaboration repairs, retained in receipts. Failed diagnostic sorryAx entries are excluded by exact source-hash selection; no new source contains sorry/axiom/admit/native_decide or resource-option overrides.

No new native window was found necessary;0 Kani/0 extraction. Kani copy mitigation, deployed features and frozen lock/graph checks are reused from NKK/NJJ native certificates within their exact domains. No Option<fn>, writable-static, field-multiplication or pending CPI-readonly credit. No source/runtime/security-contract change.
