# NEM slice S continuation handoff

Result: **50/97 composed rows CLOSED, 1/7 roots CLOSED** under the unchanged NDT/NED fixed-point rules. Started from NEL's 22/97; added 28 rows. This job is incomplete: six requested root theorems are not claimed. No push.

The CLOSED root is `validate_pool_v1_pair_forest_terminal_statement_v1`, **2/2 rows**, with theorem `NEM_ValidatorComposed.result_state_effects` (L018; full statement in NEM_COMPOSED.md). It instantiates all three reached-child laws, with no inner PacketDomain, PhysicalInterpretation or bridge hypothesis. The concrete G theorem preserves result, external state and ordered call log in one observation. Frozen native correspondence is the separately checked hybrid caller/child association, under the root's own typed domain/physical qualifications and approved P6/D188 option A. This is **trust reclassification**, not trust removal or a claim of a kernel-only Rust theorem.

## Exact remaining roots

| Root | Composed rows CLOSED |
|---|---:|
| decode_public_statement_box | 0/1 |
| validate_pool_v1_pair_forest_terminal_statement_v1 | 2/2 |
| encode_pool_v1_pair_forest_terminal_statement_v1 | 0/1 |
| reconstruct_asq8_statement | 0/1 |
| decode_pool_v1_pair_forest_terminal_request_v1 | 0/1 |
| scan_proof_buffer | 0/1 |
| emit_result | 0/1 |

The exact row denominators in NEM_STOP_AUDIT.json are authoritative if an inventory changes. No whole-root conclusion is disguised as an open leaf hypothesis. Unavailable native caller/frame proofs cannot be supplied by naming a whole-root bridge as a premise. Every remaining named member/edge/external is listed in NEM_REMAINING_OBLIGATIONS.json and NEM_STOP_AUDIT.json (all 61 members, including the 35 still OPEN).

Next in NEJ root order is decode_public_statement_box. Its native decoder/box carrier and its full1880 decoder child remain OPEN. The encoder's children are now composed, but its root native frame is not: arbitrary mutation of the same late [144,1664) window, complete returned bytes, and prefix/suffix native step association remain. Inspected NBU_K042/043: the cut returns Result<()> and its late closure does not mutate; it is insufficient. NED_CodecComposition.encoder already supplies the concrete emitted/model substitution and must be reused. Four false encoder inventory targets were resolved by exact receiver types before pruning. No decoder or result/emission bridge is inferred from an encoder theorem or a universally quantified slot.

## Budget and why work stops

**110/110 Kani, 21/80 Lean.** Kani outcomes: 50 exit0, 60 nonzero; these include expected failing controls, compiler/source errors and one compiler ICE, not 60 credited controls. Lean: 14 successful exact-source modules/audits, 7 failed attempts. The final L021 audit covers 33 new theorem names.

After the native budget was used, continued Lean-only work included same-variant scalar frames/parser state, primitive receiver width, source dispatch resolution and the complete axioms audit. Existing NEL/NEJ/NEE/NED model results were imported without re-proving them. The member-by-member under80% stop audit explains each remaining native association/OPEN child; spare Lean attempts are not represented as proof of those missing native executions. No native multiplication, SHA unwind, whole-buffer protocol-loop proof, timeout increase or memory-cap increase was used.

## Evidence and validation

- NEM_validate.py delegates all existing NDT/NED/NEE/NEJ/NEL gates unchanged and adds stricter schema-specific checks. NEM_LEDGER_DELTA.json is the overlay; NEM_REVIEWED_CERTIFICATES.json pins exact reviewed certificate contents, not a substitute for checks.
- NEM_EDGES.json contains exactly 129 internal edges: 50 certified, 79 OPEN. Edge-domain certification alone does not imply caller/root closure.
- NEM_TESTS_FINAL.log: 46 additional gate/mutation tests passed. NEM_COMPOSITION_TESTS.log: three actual full-ledger mutations (missing root, wrong edge prestate, missing child member) all keep the root OPEN. Predecessor suites are run unchanged with output only in this directory; see NEM_PREDECESSOR_TESTS.json and NEM_NEL_TESTS.log.
- NEM_ATTEMPTS.jsonl links complete per-attempt receipts containing exact command/target, exit, wall time, peak RSS, swap, revision, source/dependency hashes, limits and #print axioms. Failed Lean attempts that mention auto-generated sorryAx are excluded from every accepted certificate.
- L021: only propext, Classical.choice, Quot.sound for all 33 new theorem names. No new axiom, sorry/admit, native_decide or maxRecDepth workaround. No final frozen release replay: this is an incomplete composition job, not a release result.

K088 is an excluded compiler ICE on DST modifies. Names were not changed to affect a verdict. Fixed800 replacement kept the same names and proved universal Slice/Array poststate coverage plus same-place pointer checks. K089..098 establish all required shape-fidelity controls, including full arbitrary Result and every byte of mutation. K099/100/101 establish late tail/full Results/order/one suffix copy step and matched wrong-place/wrong-byte controls. No field-multiplication stub was introduced; there is no unpaired field stub.

KMX patch: bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67. Frozen Cargo.lock: 5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef. Each Kani launch validates exact frozen graph, deployed features, offline resolution, source integrity and unchanged lock. Admitted scopes: high6G/max8G/swap0/tasks64; Lean -M7000; optimized Rust. One scope at a time. No timed-out/memory-killed shape was rerun.

Own controllers were repaired without weakening validation: parser/frontier source corrections are retained in failed receipts; snapshot collector recursion is repaired and verified duplicate-only deletions recorded in NEM_SNAPSHOT_REPAIR.json (original snapshots/receipts retained); K103 expected failure exit corrected from10 to1, continuing at K104 without resubmission. A predecessor test wrapper that would write outside this directory was discovered before it launched; own controller/child were canceled and the unchanged test suite run directly into NEM logs. See NEM_TEST_CONTROLLER_REPAIR.json. No predecessor tracked file was changed.

## Freeze, ownership and cache

Frozen release Rust: 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. Headline RPx_Deployed.deployed/frozen3; L154 remains statement parameter; narrowed D188; RuntimePersistence retained. No 100-bit per-attempt headline result is established here; privacy/two-transaction design and trust rows are not changed. All source changes are NEM evidence/modules/patches; harness patches ran only in the own external scratch. No shipped crates/program files changed, so no ELF rebuild trigger. Inherited pins, **not freshly rebuilt**:

- default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
- devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
- Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548

Worktree actual branch: codex/cx-slice-s-compose5-20261102 (retained; task brief named an older suffix). Session A and sibling worktrees/candidate files were untouched. NEC branch codex/cx-slice-s-leaves-20261029 was unavailable at each recorded git-log check; NEM_NEC_CHECKS.jsonl retains results. No unpublished sibling closure assumed. No wallet/key operations.

Own host workspace: /home/dombarker/project-offloads/codex-cx-slice-s-compose5-20261029. Seed cache copies/hashes, including NEL priority and coherent SInt2/Aeneas objects, are in NEM_HOST_PINS.json and per-Lean pin receipts. NEM_ARCHIVE: exit0, wall0.19559411506634206s, RSS16,544KiB, swap0. **28 files (14 accepted source/object pairs)** copied with hash equality to /home/dombarker/project-offloads/codex-cx-slice-s-compose5-cache-20261029/NEM_final_objects_20261102. Only own rebuildable NEM_target/NEM_objects/NEM_tmp removed after verification. Cache, frozen source/lock and evidence retained. NEM_run.py now resolves this permanent directory before seed cache and pins it identically; path-only own-runner update required no compiler replay. Never delete the cache.
