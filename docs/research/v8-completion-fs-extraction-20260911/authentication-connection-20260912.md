# Same-body authenticated slots and chronological answer prefixes

Base: `93cab4705bc39beb8fb5649c153e2529633e270c`.
Research branch: `research/v8-completion-fs-extraction-20260911`.
The full soundness/extraction/Fiat–Shamir goal remains incomplete.

## New authentication endpoint

`SameBodyAuthenticatedSlots.same_body_authenticated_slots_or_failure`
consumes a functional Merkle run on one body and canonical parsing success
for that run's own 22 records. It constructs the decoded records (in query
ordinal order) and proves both decoded and raw gamma-batched slot equality
to the words resolved from the two commitment prefixes, or returns the existing
digest-collision / C1-late-target / C2-late-target alternative.

It no longer accepts a caller's `FixedInput`, independently supplied decoded
records, a total received word or an equality asserting that word is the
committed one. `prefixBatch` is constructed from the prefixes and body roots.
The canonical parser's successful result is still a premise, as is functional
Merkle success. Neither is currently derived from literal Rust success.
The theorem is noncomputable in the historical exact-field model; it does not
claim an efficient executable decoder or a payment extractor.

The authentication prefixes, shared hash-view consistency and log inclusion
remain explicit premises. Their probabilities are UNCHARGED. Gamma and the
query vector are supplied pointwise, not retrospectively asserted fresh.
This result concerns component batches, not yet the quotient/fold, carried
functional or final relation terminal. It is not a payment-acceptance theorem.

## What actually passed

Historical Lean 4.32.0 (`8c9756b28d64dab099da31a4c09229a9e6a2ef35`) leaf v3:
exit 0, wall 2.87s, peak RSS 6,678,156 KiB, swaps 0. Printed axioms for the
endpoint and three helpers contain only the standard foundations.
Source SHA256: `9ef7fec67c80460bb67225744ee3770ed4ffbf873cf60f61833736c0cf40ed6e`.

The run used Tailscale and a separate output directory with
`MemoryHigh=8G`, `MemoryMax=10G`, `MemorySwapMax=0`, runtime cap 600s.
Historical cache files were not edited. Before compilation, the runner checked
the 1,115-entry signature-audit snapshot and the retained restored-dependency
hash supplement against the actual files. That supplement is a **post-run
observation**, not original compilation provenance. Overlay-first import
precedence is mandatory because native-cache variants differ.

This is **PASS for the historical leaf only**. It is not an independent
first-party dependency rebuild, patched-toolchain validation, fresh kernel
replay or literal Rust refinement. The reachable historical authentication
source graph contains 308 first-party modules in the audited inventory;
Mathlib/toolchain dependencies are additional. No compatible 4.33.1 Mathlib
cache was located in the bounded workspace inventory. A pinned isolated port
and rebuild is still required for patched certification.

Evidence: `results/v8-completion-fs-extraction-20260911/auth-slots-historical-v3/`.
`HistoricalLeaf.py` records the command, search path, input hashes, compiler
result and metrics. It refuses an existing output directory and validates
historical inputs before compiling solely the new target.

v1 and v2 failures and exact source snapshots are preserved in sibling
directories. Both stopped at the existential result construction: case
analysis had already rewritten the successful parser result, but the proof
supplied the old `hd` equality, leading to deep definitional comparison of
the concrete parser. v3 supplies the reflexive equality of the rewritten
result. Small projection lemmas introduced in v2 are retained. No recursion,
heartbeat or memory limit was raised; the endpoint statement was unchanged.
The original source header retains its draft status: this report distinguishes
the subsequent historical leaf check from the still-missing source rebuild.

## New FS producer

`FSAuthenticationPrefixes` constructs both 26-byte answer prefixes from the
actual cuts of the full-answer `constructBoth` interpreter. It proves exact
prefix lengths/takes and consistency with the same final full-answer cache,
without assuming injectivity of digest truncation or caller-supplied inclusion.
Tests deliberately retain distinct full answers sharing a 208-bit prefix.

In addition to the agent's focused compile, the six-module first-party source
closure was rebuilt in a fresh temporary directory using Lean 4.33.1. All six
targets exited 0, standard printed axioms only. Evidence:
`results/v8-completion-fs-extraction-20260911/FSAuthenticationPrefixes-w_fgtx74/`.
Reproduce with `FocusedLeaves.py --root FSAuthenticationPrefixes` from this
directory. This new root has **not** received a fresh kernel replay. The
historical field/authentication graph was not imported into this Std-only run.

These two successful results are not silently composed: the FS final log
currently ends after C2 absorption, whereas the authentication theorem needs
later opening calls too. Conversion from literal byte inputs to the historical
`RawHashInput` grammar, the shared effectful opening log and its actual source
producer remain open. Default values in `totalView208` are never evidence of
answers for unqueried inputs.

## Dependency correction and next step

`PackedQueryResidual` is an uncompiled historical draft (v1–v9 failures), not
a checked dependency. It is absent from this endpoint's imports. The checked
`SelectedPackedQueryBridgeV3` arithmetic is the next consumer, but its
post-query `observedWord` must be replaced using the authenticated slot
equalities—not treated as an early fixed oracle by assertion.

Next: transport these same-body slot equalities through checked chord
inversion and the actual four-slot fold, then feed their outputs into the
positive query-scalar and functional update. In parallel extend the actual
FS history past C2 and construct the authentication grammar/log bridge.
No new probability bound, production edit, protocol change, CU claim or ZK
claim. Proof body remains at most 40,282 bytes; grinding credit remains zero.
