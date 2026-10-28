from pathlib import Path
import json
E=Path(__file__).resolve().parent
p=E/'NDI_HANDOFF.md';s=p.read_text()
summary='''# Final handoff: lane 3 continuation, NDI_

Five new CLOSED-CONDITIONAL local bridges: ValidatedRecord::row, the actual SolanaDigest transcript state getter and initializer, QueryGeometry::for_query, and batch_keys. Six NDF local bridges imported unchanged:11/24 representatives locally closed,13 OPEN,zero composed closures. S2 and AspisR1.RPx_Deployed.deployed remain OPEN; the 100-bit per-attempt release target is not established. P6/D188 native contract semantic transport is an explicit trust reclassification, never a removed premise. L154 remains a statement parameter; runtime hash values and RuntimePersistence retain their approved trust rows. No privacy, game, or two-transaction design change.

Final usage:80/80 actual Kani invocations,78/80 Lean runs,6/20 extraction runs. Ten source-preflight refusals are separately recorded and consumed no Kani invocation. Native outcomes:29 positive passes,31 expected negative controls,15 timeouts,5 compiler/input failures. No unchanged timeout retry or cap increase. All174 admitted scopes use High6G/Max8G/Swap0/Tasks64; every Lean command has -M7000. All recorded swaps0; peak RSS6,496,908KiB. Each immutable receipt records exact target/command, exit, wall time, RSS/swap, source revision/hashes, limits and axioms. NDI_ATTEMPTS.jsonl indexes and hashes those full receipts.

Final focused audit NDI_L078: exit0, wall3.020499918s, RSS4,411,892KiB,swap0. All67 new top theorems across42 current accepted modules use only propext, Classical.choice, Quot.sound. NDI_PROVEN_MODULES.json links each exported source under lean/NDI_ to its successful source receipt; NDI_Audit.lean prints the complete theorem list. Final read-only postflight checks5,384 selected objects/tools/library/manifest files and1,159 private native source files. Historical L001..L032 directly invoked lake with recorded selected pins; L033 onward adds the dedicated per-scope dependency gate. The final union rehash covers both, with no invented historical preflight record (NDI_VALIDATOR_REPAIR.md).

Own receipt/pending-overlay validation passes (NDI_VALIDATION.json); official NCZ stage6 exits1, “merged report corpus changed; refresh evidence snapshot explicitly”. Its immutable BASE snapshot rejects the expanded report set before inspecting this overlay. Shared validator and canonical rows were not changed. NDI_LEDGER_UPDATED.json retains canonical rows plus NDI_pending_delta; canonical adoption still requires the lead's snapshot refresh. This local validator is not a replacement NCZ pass.

NDI_ISOLATION.json/NDI_SOURCE_DRIFT.patch document the inherited external scratch symlink defect, detection before K056 launch, private frozen-source repair, and timing after K055. K056..K065 are preflight-only refusals. Post-isolation native gates check private regular sources before AND after invocation. Every native invocation retains frozen resolved dependency/deployed-feature graph, offline environment, unchanged frozen Cargo.lock, and exact KMX patch/source hashes. Missing immutable receipt source snapshots were recovered read-only into NDI_receipt_sources.tar.xz, checked against each receipt and indexed in NDI_RECEIPT_SOURCE_ARCHIVE.json; .tar.sha256 hashes the uncompressed original.

No repository crates/ or programs/ changes: both trees remain byte-identical to frozen4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. No ELF rebuild trigger; inherited pins remain default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4, devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299, Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548. Native harness/source changes are scratch-only, archived as NDI_harness.patch/NDI_scratch.patch plus receipt snapshots. No keys or funds were created, moved or deleted.

Host continuation: /home/dombarker/project-offloads/codex-cx-native-front3b-20261028. Own retained cache: /home/dombarker/project-offloads/codex-cx-front3-cache-20261028. NDI_objects now links to that cache's NDI_objects;45 object files retain identical hashes (42 modules plus audit, diagnostic and privately compiled unchanged S7 prerequisite). Read-only inherited NDF/NCO and coherent SInt2 objects remain pinned. Cleanup removed only own NDI_target, NDI_ref_target and NDI_tmp, reclaiming3,072,973,456 bytes; source, receipts, LLBC and cache remain. Recreate own NDI_tmp before a future authorized run. No active lane scope at cleanup; no shared files, cache objects or another lane's /tmp files were deleted. NDI_CLEANUP.json records paths/hashes.

Remaining members and why unused Lean/extraction allowance cannot close them without new native evidence:

|Member|Exact next obligation|
|---|---|
|update_residue_row|Actual arbitrary-prestate limb iteration and raw primitive-product call log, tied to existing residue induction and caller bounds. These raw products are not licensed field-call stubs; never multiply them in Kani.|
|mark|Option<fn>/observer quarantine remains binding. Lean None identity or renaming cannot restore native credit.|
|sample_block_validated|Accepted-path ACTUAL native contract remains unproved after distinct full/branch/borrowed/output/state attempts timed out. Ordered runtime call/reply and rejection constituents plus all current Lean value/domain laws are green. A fresh smaller native dependency split is required.|
|circle_fold_with_inverses|Actual opaque-call log, canonical callee domains, matched native controls and paired emitted field laws. Reuse merged NDD callee bridges; no field multiplication Kani.|
|line_fold_with_inverses|Same native log/domain obligations, including iz and half/quarter calls. Existing model arithmetic is not native sequencing evidence.|
|batch_prefix_products|Native arbitrary one-append/one-product iteration, Vec frame/copy controls and same product-log association. Existing prefix induction is retained; Vec-return substitution is unsupported.|
|parse_record|Actual native framing/header/validator iteration and full first-error Result association; borrowed Result substitution is unsupported. Full all-row/all-slice reference/cohort assembly is proved at L019/L020.|
|BatchedWeights::finish|Actual one-destination-write iteration and typed mutable frame/source association, invoking the already closed value callee inside its domain. Existing finish induction alone is insufficient.|
|parse_shape|Original seven-byte any trace and full length/magic/tag/Result branch association. Tail predicate, iterator metadata and symbolic tail/window laws are constituents only; no whole-loop native run.|
|Reader::raw|Original arbitrary backing/cursor native association. Full1768-backing attempts timed out; exact-size4/16/32 windows and slice metadata do not establish caller-domain relocation. Model/selected-byte/cohort laws and concrete offset bounds are complete.|
|read_checkpoint_semantic_alpha|Real raw/k callee packet, exact cursor/first-error sequence and matching fixed-array Result shape controls. The native reader dependency is OPEN.|
|read_checkpoint_weights|Real one-element decode/write native packet with mutable Vec frame and raw/k caller domains. The native reader dependency is OPEN; Vec-return substitution unsupported.|
|validate_checkpoint_queries|Actual arbitrary outer iteration and U32 prefix membership implementation path. Singleton contains and U8 iterator metadata do not cover that path. Existing model iteration/induction and new predicate/emitted-model associations are complete.|

No remaining attempted split has an unfinished Lean-only obligation: finishing the above rows requires native/source-interface facts or a quarantine decision. Two Lean and fourteen extraction allowances remain unused; new reference extraction cannot supply those missing native facts. No incoming parent trace, same-execution ownership, runtime realization or source-to-ELF obligation is silently discharged. All stage commits are local; nothing pushed.

Historical stages follow (their budgets/statuses are checkpoints, superseded by the final totals above).

'''
assert s.startswith('# Frontier lane 3 continuation');p.write_text(summary+s)
