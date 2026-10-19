# Stage2 extraction frontier — failed candidates

CANDIDATE/FAILED, no accepted theorem. This packet preserves the exact source inputs, tool-source patch hashes, commands and receipts needed to avoid repeating the same failures. Executables, LLBC payloads and object binaries are not included; their hashes are retained. Full stdout is pinned by hash/native path; only its first35lines are copied. None of the source/tool edits below changes production Rust or an accepted Lean owner.

- Unchanged finish_relation: Charon succeeds. Existing extended Aeneas fails with Not_found at shared-borrow merge; the recoverable circle-join tool reports the same missing projected abstraction. Existing October return-pass reuse does not fix it.
- Tool projection-omission candidate v2: REJECTED. It passes the first lookup but later fails context matching; it is not used by any accepted proof. Combined tool v3 reuses exactly the two retained October return functions plus the predecessor recoverable diagnostic patch; it does not include the rejected projection edit. Its complete source-file manifest, patches and capped build receipt are retained.
- Source candidates: per-round inline helper, indexed dot loop, both indexed loops, and helper+indexed loops all still fail Aeneas. None is viable evidence for changing the frozen verifier. No source-equivalence or CU test is claimed.
- Adopted tx2_common: Charon succeeds; Aeneas fails at finish_relation(&v,&p,&a,obs) after pending.finish(&mut a.weights), reporting a bottom in the whole Accumulator value. The successful outer tx2_authenticated wrapper is proved separately, with the common caller as an explicit boundary.
- Adopted resume: the first kit failed Rust compilation due to a missing module-layout import; corrected v2 passes Charon and fails Aeneas with an escaping mutable region. The Reader::raw/e/k source leaf is extracted and proved separately with explicit decoder/unwrap boundaries.

The exact unchanged finish_relation body equals the adopted c8ea8dd49 body (byte-hash continuity recorded). Tool-only attempts reuse their predecessor Charon LLBC and receipt: copied receipts are labelled in attempt-index.json and are not additional Charon executions. V7's 8GiB request failed admission before Aeneas started; V8 used a 2GiB max based on all predecessors staying below200MiB, with no OOM or cap increase. All started scopes had swap0 and no memory-pressure kills. The legacy human-readable reservation note is stale in some receipts; exact checked limits and admission JSON are authoritative.

Next source-closure work is genuine borrow/callback lowering or a proved compatible iterator/state model. Re-running these unchanged source candidates is not useful. This packet proves neither full R14 nor 100bit soundness.

Admission snapshots are published as aggregate summaries to avoid duplicating unrelated host-service inventories. Their original full hashes and retained local paths are explicit; no individual foreign service accounting is changed. Original snapshots remain on the NUC and in the retained local collection.

Exact .patch files retain unified-diff blank context lines (one space) and their source hashes. Display log excerpts normalize trailing whitespace; full unmodified logs remain hash-pinned.
