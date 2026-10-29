# D426 ownership continuation — final report

**V229 SUSPENDED; V230 SUSPENDED; V239 SUSPENDED; V178 SUSPENDED. No row restored, no checked native witness-dependent FINDING, no endpoint premise removed. Privacy target not yet established.**

Exact sparse worktree `/Users/dominic/ZK/.worktrees/pv-own`, branch `codex/pv-ownb-20261029`, candidate/base `07f4f723d8`, inherited WIP `0cdb792b74`. Both automatic relaunch messages were treated as continuation of the same fresh D426 budget. Prior WIP and host inventory had used zero Lean/native attempts. This continuation used **100/100 Lean starts, 2/60 capped native/housekeeping scopes, 0 Kani**. See [COMMITS.txt](COMMITS.txt) for the path-limited commit history through evidence preparation; the final report commit follows it.

## Checked result and its exact scope

`PV_OWNB_KindCodec` retains all 21 kind variants, every payload, producer and consumer. Independently compiled per-variant read lemmas compose into active-byte decoding and uniqueness. `LinkBytes`, `LinkFields`, `LinkUnique` and `LinkCodec` establish an eight-byte/two-alignment **candidate representation**. `Padding.Agrees` constrains only active representation bytes: inactive payload bytes and trailing padding may be initialized arbitrarily or uninitialized. `PaddingBridge.exact` supplies an explicit canonical view projection to the inherited exact-snapshot interface, not an actual native mutation or an unproved world equivalence.

`Cursor` describes one exclusive internal allocation scope with current owner/generation, a written prefix, and an unread tail. Per-stage proofs establish read-before-write, initialization, prefix/tail frames, generation preservation and consuming ownership transfer. `WriteProducer`, `WriteConsumer` and `Relocate` prove distinct two-byte endpoint stores and preserve kind and padding. `ActualSink` and `ActualResult.complete` permit arbitrary padding choices; the active-byte copy law is an explicit hypothesis, not an allocator assumption. `ReadSnapshot` derives that law from current represented memory. `SnapshotResult.complete` composes its symbolic induction with the complete **full-Link** filtering value law without a copy-callback hypothesis. No concrete 127-link recurrence was kernel-normalized.

`CursorCleanup`, `CursorExit`, `CleanupConsumed`, `NoDoubleCleanup` and `CleanupRetired` establish the explicit model's POD backing-store cleanup, current owner consumption, post-state retention on primitive failure/divergence, error continuation, direct abort-handler execution and exclusion of a second deallocation through the consumed slot. These are model equations, not proof that every native unwind edge is already associated. In particular, retirement on every primitive outcome is inherited primitive-model behavior; its actual runtime adequacy is not proved here.

The 76 new development modules are mathematically checked. Names such as `complete`, `ActualResult` and `SnapshotResult` do not imply a native implementation instance. The source scope is the collector's filtering stage and local endpoint stores, not the entire V229 callback.

## Measured source and native evidence

[deployed-collector-sources.json](deployed-collector-sources.json) captures the deployed 1.94.1 in-place collector, source iterator, drop guards and specialization source. The source read cursor advances before a destination write. Normal completion disarms the prefix guard, establishes the destination-data/source-buffer guard, clears source allocation ownership before tail destruction, and transfers the unchanged equal-layout allocation to the returned Vec. Source inspection does not substitute for that native-to-model proof.

Native01 built with rustc **1.94.1**, deployed dependency versions and resolved feature union, release opt3, debug assertions/overflow checks off, panic unwind. [native-result.json](native-result.json) records all crate features, compiler, source checks and MIR hash; [native-01/output.log](native-01/output.log) retains compiler type-layout output. The active-field probe passes **67,086 cases**, including every SpongeCarry payload pair and all single-byte payloads. It confirms Link size8/alignment2, endpoints at0/2, kind at4 with size3/alignment1, and no Link element destructor. It never reads padding. This is **finite validation plus compiler layout evidence**, not a universal native memory law or a complete structural K-1 substitute. No new extraction, Kani, or copy/function-pointer PASS was consumed. The inherited native suites were not rerun unchanged.

## Whole-row dispositions, in requested order

- **V229 — SUSPENDED.** Before: shared exact-byte interface and logical-cell resource/value program, with no full Link padding/cursor law. After: checked full-kind candidate codec and padding-aware byte/read/write/filter/ownership model, including local cleanup equations. Still missing: universal deployed layout and source-specialization/carrier association; native raw read/write/cursor binding including all guard/unwind transitions; complete relocation/reserve/push/FlatMap/sort/dedup initialized-byte and owner transport; every whole-callback Result/error/abort continuation; and composition with **PV_RDB2D_CollectorProgram.complete and its value law**. That composition was not performed. The read-only import inventory identifies its31-module tracked cone; it is not a source-authority or compiled-cohort certificate.
- **V230 — SUSPENDED.** V229 association plus actual deployed usize/u16 shift, OR and stack-array/selected-op134 carrier association. No restoration follows from the model's POD cleanup or fixed mask values.
- **V239 — SUSPENDED.** Native sparse Vec initialized-length/header/byte/ownership instance; raw ordered QM31 methods, arbitrary monadic builder cardinality, dense/sparse transport, and public point/length at the consuming protocol call. No new V239 closure is claimed ahead of V229.
- **V178 — SUSPENDED.** Native owned-name/move/Path::join cleanup binding into the byte/world relation, plus deployment-wide diagnostic reachability and public provenance of diagnostic arguments, headers and guards. Inherited source/model results retain their documented qualification.

No same-public admitted witness pair with differing destructor/allocation occurrence, order or size was established. Unproved dependence is suspension, not a native FINDING. No witness-domain, observer, simulator, dictionary, failure event or endpoint statement was altered. Endpoint premises removed/added/changed: **0/0/0**.

## Trust and resource boundary

Any compiler, MIR, Aeneas or Charon agreement with Rust semantics is **reclassification within existing tool trust**, not premise removal. rdea-1 retains allocator/runtime primitive outcomes, fresh aligned disjoint ranges, realloc-prefix preservation, actual deallocation and default handlers under the existing runtime item. Native typed stores, source ownership and concrete continuation association remain proof obligations. T stays exactly **entropy_law, entropy_kernel, observation**. Compiler/executable D381/D386, E1/E2, real RunJoin, proof-account routing and L1/L2/L3 remain obligations. No new extraction was attempted, so no extractor/toolchain substitute bypassed (x').

All actual scopes checked admission and the in-scope barrier, used MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64, and ran one at a time. Lean used -M7000. No cap was raised; no memory kill, timeout or unchanged failed-proof rerun occurred. The output-directory repair after62500 changed that failed attempt's environment before62501. Remaining rejected attempts changed their proof source before retry. The eleven failed starts, including recovery-output sorryAx, earn no proof credit.

## Final verification receipts

[combined-audit.json](combined-audit.json) and numbered receipts retain exact target/command, exit, wall, peak RSS, swap, source revision/blob/SHA, dependency fingerprints and axioms output. **89 Lean starts pass,11 fail.** Maximum Lean RSS519888KiB; native build RSS541576KiB; all swaps0.

|ID|Exact module|Exit|Wall|Peak RSS KiB|Swap|
|---|---|---:|---|---:|---:|
|62597|R1Z/PV_OWNB_StatementsAudit|0|0:00.27|490420|0|
|62598|R1Z/PV_OWNB_AxiomsAudit|0|0:00.17|489116|0|
|62599|R1Z/PV_OWNB_FocusedReplay|0|0:00.17|493388|0|

All three use source revision **a90198df909e896270b6d3802558b7ade30e5c28**. Statement audit checks118 new development theorems and prints complete root statements. Axioms audit's118 queries use only subsets of **propext, Classical.choice, Quot.sound**. Focused replay composes the final snapshot byte/value root and audits its supporting ownership/cleanup roots. This is the one frozen **model-closure** replay, not a release/privacy-endpoint replay.

External authority verification checked all5673 objects before the first compile (historical JSON retained in83cf441944), and again before audits. The current verification JSON retains the helper's stale label “before any resume compile”; its timestamp is the final pre-audit verification. [final-fingerprint.json](final-fingerprint.json) checks88 private project objects, current tracked source identities and every direct/transitive project edge. No other job's project object was reused; no shared object/source or library was rebuilt or overwritten.

## Process receipts and limitations

The first WIP ID preflight accidentally ran locally and scanned zero host directories; its RSS is in Mac units and is not a host resource receipt. The host scan after62501 covered60,732 directories and shared sent files, found no collision, and the final host scan also finds none. This is reported as a late correction, not an adequate initial host scan. FullResources/Box source review was completed late; neither was consumed for new closure credit.

62530's barrier refused before Lean at00:24:22.722245 UTC. Same-ID retry under ruling(m') was admitted at00:27:33.929528, **191.207283 seconds** later. No actual scope occurred during the cooldown. The task wrapper was strengthened to inspect allowed:true explicitly in the same-shell launch-admission JSON as well as exit0; recovered earlier launch admissions were all allowed:true. No ruling(t) violation was found. Limitation: the same-ID retry overwrote the raw refused barrier JSON and queue log. Its decision/time were recorded in RESUME.md and the conversation tool output; they are not represented as a surviving raw JSON receipt. Historical target-list files are scheduling records; numbered submissions and receipts are authoritative.

[cleanup.json](cleanup.json) records88 own project objects (14,098,400 bytes),21,987 external-object links and203,891,239 Cargo-target bytes removed after final fingerprints/replay. Sources, MIR, source snapshots, raw successful/failed compiler receipts and executable hashes remain. No wallet/account key was created, deleted or modified. No crates/programs, protected soundness file, dictionary, simulator or observer was changed; no XR imports, new axiom, sorry/admit/native_decide/implemented_by or raised limits. No committed file exceeds20MB. No push or merge occurred.

Stopped at **100/100 Lean attempts**. Next concrete deliverable remains the complete **native V229-to-PV_RDB2D resource/value association**, using the checked full-Link padding/cursor lemmas and preserving all subsequent stores and destructor/error/abort stages. The new model alone does not restore the row.
