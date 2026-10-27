# Batch3b LOG D316 — stopped on native fixture disagreement

Exact worktree /Users/dominic/ZK/.worktrees/pv-l3, branch codex/pv-batch3-20261027. Entry d4251d80303af9ee024a6da046ee5909d4aa631f; the earlier required merge was already present. No push. Source/proof history through the rejected Rust freeze is COMMIT-LOG-batch3b.txt; later commits contain evidence only. Previous handoff is preserved in RESUME-HANDOFF-before-batch3b.md.

## Mandatory stop, rejected candidate, last passing source

Rejected source: **0b048ee98d531103b22dc99c22df6b687ef9e0a2**. Native optimized gate batch3b-split-bench-02 exits101: copy::build_pool_v1_pair_forest_copy_row_schedule_v1().unwrap() receives Err(Shape), before any timing sample. Receipt:19.768s, peak RSS528832KiB, swap0; full stderr retained. The source rewrite erroneously expanded20 legacy private-path levels while frozen POOL_V1_PAIR_PRIVATE_DIRECTIONS is21. This omits level20's three links:124 versus the required127 legacy links. This is the worker's rewrite error, not a counterexample to the original frozen ROWS5 statement. The original source is unchanged.

Stop reason is the prompt's **fixture-disagreement stop**, not budget exhaustion or a failed candidate lemma. No source correction, further compile, extraction, audit replay or native test was run after discovering it. The bad candidate remains committed and unadopted. Do not merge/adopt it. Do not repair it by weakening the127-link shape check.

Last fully passing Rust/cost freeze: **c97270adc2b3653dbc7ce65a1b8811722f3c2088**. It passes all native inventory/helper/public/terminal comparisons (both variants, all11 terminal point shapes). Its cumulative measured fixture projection is transfer+1.9023712534770507%, withdrawal+1.906124819123782%, against14.38s. This is a per-call projection, not whole-prover timing or a formal cost bound. The rejected source has **no valid cost projection** because its gate stopped before measurements. No unchanged timing rerun was used to select lower noise.

## Budget, receipts, provenance

15/100 charged Lean attempts:11 accepted,4 rejected;85 unspent.0 Kani. First extraction phase used15 of its40-attempt ceiling; the later op134 and117/121 phases were not reached. IDs37900–37915 were consumed, including admission-only refusal37907 (charged0); next37916. Audit37997–37999 remain unused because of the mandatory stop. Charon132-b3b05 and terminal-elf-01-default also had admission refusals; each cooldown was at least180seconds. No scope overlapped another scope in this job. Caps6G/8G/swap0/Tasks64, Lean-M7000, optimized Rust, pinned unchanged Charon daad69be… / Aeneas562e1f51… throughout. No local Lean.

Before the first compile, all5673 external objects were SHA-checked against research's coherent replay manifest. A second check verified actual env-J resolution selected matching objects. See batch3b-external-verification.json and batch3b-resolution-verification.json. No library rebuild/substitution or shared source/object write. New Lean modules use PV_B3_. The proposed later op134 imports R1Z.PV_Op134_MaskSpec, R1Z.PV_CBM_MasksSelection and R1Z.ProverRwFullExternalFuns were held: no authority was found in checked EJR/commit47/54/55 records; a request for the committed freeze record remains pending. They were not imported/compiled in this run.

batch3b-receipt-index.json retains exact target, status, wall, peak RSS, swap, source SHA/revision, dependency hashes and complete raw axiom logs for every Lean attempt. Maximum Lean process RSS2652740KiB, swap0 throughout. Every accepted declaration uses only propext/Classical.choice/Quot.sound or no axioms. Rejected37901/37905/37906/37915, including automatically generated sorryAx diagnostics, are retained and excluded. batch3b-current-source-coverage.json lists matching accepted snapshots; the current EvalRank222 correction and EvalFinite222 remain uncompiled drafts.

All six source stages rebuilt all three release ELFs:18 matching pins, including the rejected prover candidate (its changes are gated from release programs):

- default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
- devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
- Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548

## Exact progress and residuals

222: unchanged pinned tools emit the actual root, sparse-weight construction and evaluation loops. Types37900 and ported Funs37902 pass;37903 proves that the total U32 shift-count cast preserves the low six bits.37904 proves the complete Result wrong-length branch, with empty-column non-vacuity (not a successful row witness).37908 directly executes the emission on an all-zero point/constant-seven column and gets ok(some[7,0,0,0]).37911–37913 prove the suffix scan's counter, decreasing rank and complete-Result bounded factorization for arbitrary raw inputs.37914 proves the evaluation-loop counter relation. Original/copy equality and the row law remain unproved.

Ruling(n),222: its sole data write is Array.update and the updated array is threaded into cont. No mutable iterator/restoration is discarded. The identical-input native/emission differential remains pending: fidelity222-native is written but was not run before the forced stop. Existing native original/copy11-shape benchmarks pass; they do not substitute for that same-input comparison. No source-law fidelity credit is claimed.

132/133/228: retained unchanged-extractor context-join failures, most recently in the legacy schedule loop at source5.226: retained SymbolicToPureAbs failure on the projection at source5.227: structured Drop was removed; source5 still refuses escaping reference output.224: Vec/slice indexing methods return references; no placeholder, guard bypass, extra trust, or malformed-input behavior change was introduced. Source6's further changes were never extracted because the fixture gate failed first. Originals and117/121 arithmetic copies remain unchanged.

Rows closed0. Before/after V217,V220,V228,V229,V230,V239,V241,V243,V244,V245 all remain P/OPEN with the same ExternalFuns residual. No premise removed, added, weakened or installed. T remains exactly entropy_law,entropy_kernel,observation. Native source/dictionary association, universal117/121 equality, D234/V403, runtime/deployment/E1/E2/RunJoin and L1/L2/L3 remain open. Target not yet established.

## Retention and next deliverable

No own scopes remain. Current objects were inventoried before private target/charon-target/sbf-target/lean-objects caches were removed. Source, raw LLBC/emissions, receipts, ELFs and counterexample binary remain; the binary is bin/batch3b-split-counterexample, SHA256 fe278db2829e72ecbbbc61702042427c6152d9f9341702965c8aa457bfad54a3.18 generated build keypairs remain0600 in artifact directories. No keys, funds, authorities, nonce ledgers or shared paths were deleted. See batch3b-cleanup.json and batch3b-object-inventory.json. No binaries or keys are tracked.

Next authorized continuation: correct the legacy bound to the frozen21 steps, retain this failure, repeat all-three-ELF/native/cost gates, then extract the actual roots before claiming source laws. Clear h4 project-source authority before op134 dictionary imports; then continue134 association/installation and117/121 universal equalities/row bridges.85 Lean attempts remain from this allocation, but no further work was done past the required stop.
