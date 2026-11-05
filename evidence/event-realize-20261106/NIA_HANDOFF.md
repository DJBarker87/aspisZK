# NIA event realization handoff

Branch: `codex/cx-event-realize-20261106`. **PARTIAL: model packets proved; native realization remains OPEN. Target not yet established. No row promotions.** Stage commits are local; no push or merge.

## Exact results

- `NIA_EventInterpretation.lean`: all twelve NFP event cases represented on the complete NFS_CallerDomains.ops selection; no_seed independence, structural no-read traces and arbitrary-context frames. This proves the interpreter, not its native purity/trace association.
- `NIA_ScalarEffects.lean`, `NIA_ConstructorOpening.lean`, `NIA_ConstructorTrace.lean`: complete source-order MODEL syntax and exact NGN_Emitted.prepared Result/Trace for every branch, without a successful-constructor or complete-Trace premise. Seed, scalar/replay, query and rho events are retained. The actual claim's dictionary independence is proved. Box allocation is erased at this extracted endpoint and is not certified.
- `NIA_ScalarFailures.lean`, `NIA_BlockCoverage.lean`: primitive tag/absorb/read/advance fail/div packets, exhaustive block model coverage, exact scalar/scalar_k Result and occurrence-log frames. Existing NGT ok laws are unchanged. These are partial-model packets, not native Rust Err certificates.
- `NIA_QueryPrefixes.lean`: the SAME NHS opening and NHK query invocation give constructor query Error/fail/div traces with exact earlier++observed.attempted, no invented suffix and correct scratch.
- `NIA_DriverPackets.lean`: packet exports fit unchanged NHZ_DRIVER.Cuts; conditional events_from_constructor literally invokes events_from_cuts. It retains the full code ordering premise and constructs a model observation, not a physical TX1 witness.

## Validation and pins

`NIA_COMBINED_IMPORT.lean` imports the complete new forest with NGK_COMBINED_IMPORT and AspisR1.RPx_Deployed.deployed (L023, exit 0). L027 raw ax2 traversal: all 49 roots agree with collectAxioms and use only propext/Classical.choice/Quot.sound. L026: all eight fixture controls pass. L028 NFX-style scan: 13,653 modules, exit 0, zero dangling references, incompatible owners or import mismatches. NIA_validate.py passes receipt, final-source, admission, cap, axioms, fixture, scan, size and non-promotion checks. Failed draft receipts are retained and excluded from credit.

Every launched scope has exact command, target, revision, source/dependency/Aeneas hashes, exit, wall time, peak RSS, swap, cgroup and printed axioms in its receipt. Total 28 support scopes/80, including 22 Lean compilation scopes, 0 Kani/40, 0 extraction/1; two prelaunch-only input failures are recorded separately. Aggregate wall time 165.96 s; largest peak RSS 7,103,740 KiB (scan), swap 0. No timeout, memory kill, cap increase or unchanged regression rerun. All jobs were serial and admitted with exit 0 AND allowed:true, inside 6G/8G/0/64 scopes; Lean -M7000.

Cache seed: 123 files, 18,625,312 bytes, imported hashes in NIA_CACHE_IMPORTS.json.xz/NIA_SETUP.json. Export: 1,313,648 bytes of new owned objects; NIA_RESTORE_PATHS.json restores them. NIA_CLOSURE_PINS.json.xz pins the selected 30,246 object/sidecar files (7,645,644,288 bytes) and 240 Aeneas/AeneasMeta files. NIA_TOOLS.json pins tools and the audit driver. Only own rebuildable workspace outputs were removed after verifying exports; the private cache was retained. Host disk was 97% used. No shared cache or infrastructure was edited.

## Remaining and next deliverable

See NIA_REMAINING.md, NIA_FAILING_STEP.md and NIA_HYPOTHESES.md for member-by-member scope and below-80% disposition. Native NFS cut-to-query-effect association, native constructor logging installation, the scalar syscall/abort partial-semantics boundary, and Box abort prefix remain unproved. Frozen Digest32/scalar/scalar_k return fixed values, not Err; short scalar payload is not rejected by their source. A clarification of the intended native failure boundary was requested while independent work continued. An Err-returning logger at those signatures would change the interface, so no invalid native harness was launched. No Kani/extraction exhaustion is claimed as a stop.

NHU/NHW op9/full native parent ordering and NHZ same_law's five physical-observer fields remain external. No assumption, cryptographic bound, trust row, metric, privacy condition or two-transaction design was changed or removed. No schedule mismatch is established. Source-to-ELF/runtime/compiler/SDK/Std/allocator and narrowed P6/D188 trust remain explicit.

All changes are NIA-prefixed files in this evidence directory. No shipped source, ELF, wallet/key, session A or sibling worktree changed; the ELF rebuild trigger did not fire. Historical pins are inherited only (NIA_STUBS.md), not newly reproduced. No file exceeds 20 MB; no __pycache__ is committed.
