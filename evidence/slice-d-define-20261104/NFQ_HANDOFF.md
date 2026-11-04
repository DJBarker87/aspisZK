# NFQ slice D handoff

**16 functions / 21 D occurrences are CLOSED under the adopted hybrid and retained root trust boundaries. The driver root remains OPEN. The deployed 100-bit per-attempt target is not yet established.**

Branch `codex/cx-slice-d-define-20261104`. No push, merge, shipped-source, session-A worktree, wallet/key, chain or shared infrastructure change.

## Definition and exact coverage

`NFQ_SLICE_D.json` uses the original VERTICAL-SLICES schema and canonical UNION call graph. It reproduces Q=78 and S=61 exactly. D is the deployed common-entry cone minus their function sets: **295 functions, 448 internal edges, 343 occurrences**. Both TX1 and TX2 dispatch through `programs/r1-cost-probe/src/lib.rs::process_r1_cost_probe_instruction`. TX1 accepts `[3,10]`/`[3,11]`; TX2 is ASQ8-prefixed. Disabled legacy `first`/direct `tx2` branches are not the deployed roots.

D union Q union S covers **585/587** inventory rows. `TX2:046` is unresolved trait `WideExact::from_m31`; `TX2:211` is the omitted `map_err(error)` callback. The six additional TX2 rows with only canonical-union paths have membership but no transaction-specific reachability proof. Pool settlement is outside the 587-row verifier inventory, a recorded boundary owned by NFO. These gaps are not silently repaired or declared unreachable.

All 343 D rows were OPEN in NFK, including the twelve D opaque leaves. The thirteenth leaf, Dot::push, is in Q. `NFQ_LEAVES.json` records all KNF statuses. DrvI counterexamples and DrvC installed-model evidence do not close a new D native occurrence. The original per-transaction NFQ draft (291/441/339, 581 covered) is explicitly superseded by the union-graph correction.

## Certificates and validation

The first five selected helpers all closed: compact_row, row_shape, Variant::folds/final_len and checkpoint_size (8 rows). Eleven more closed: readonly_buffer_meta_ok, M31::neg/reduce_u62, CM31::from_m31, QM31::from_cm31, PreparedQm31Multiplier::new, variant_expected_output, copy_variant, extension_limbs and WideExact::c0/c1 (13 rows).

`NFQ_CLOSED.json` lists exact domains and native/control/model roots. `NFQ_CERTIFICATES.json` and `NFQ_EDGES.json` provide occurrence-specific complete recipes and call-domain discharges. `NFQ_certify.py` invokes unchanged NFK certificate checks, materializer, row checks and admission, adding frozen-body, graph/lock, controls, KMX, complete-value and ax2 gates. Frozen body byte ranges are checked in both native/control source snapshots. No credited body uses stub_verified; native real callee bodies execute. Receiver alternatives in Prepared construction are resolved by concrete CM31/M31 types; canonicality is proved for every actual addition.

NFK-anchored totals become **240 CLOSED, 2 QUALIFIED, 345 OPEN**; D has **21 CLOSED, 322 OPEN**. This delta preserves every other occurrence status. Later NFN geometry and NFM dot results are cited separately; their Q credit is not duplicated. S's seven roots retain NFJ's cumulative checked closure. Q query_loop remains an OPEN boundary pending NFP.

L010's six raw roots are reused. L048 imports all 36 new theorem roots with the coherent headline/NFN objects and prints standard axioms. L050's single capped audit links an optimized driver, passes all eight planted/mutation fixtures in that binary, and fully walks all 36 new roots in five groups. Every walk equals collectAxioms with only propext/Classical.choice/Quot.sound; projection/roundtrip and several other roots have no axioms. Walker bytes are unchanged. Raw graphs are xz plus sha256; driver diffs, binary pins and child resource receipts are retained.

Excluded from credit: cm31_mul_r K050/K051 has a direct value certificate, which does not meet the prescribed field-product opaque-call-log form. require_zero K058/K059 is one length0..4 native result fragment; K060's pointer fact lacks a matched control. Full finite-loop reference/model equivalence, acceptance/rejection induction and arbitrary-index model step laws are proved, but generic native physical/frame lift is missing. Both functions stay OPEN. No field multiplication was proved in Kani and no unpaired multiplication stub is admitted.

## Frozen target and retained assumptions

Frozen Rust: `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`. Cargo.lock: `5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef`. Every native run validates frozen resolved package/edge identity offline before launch and lock identity afterward. Actual feature closures and source assessments are in `NFQ_FEATURE_PARITY.json`. Native harnesses/annotations live only in an external scratch copy and are committed as patches/inputs/receipts; repository crates/programs remain unchanged. The exact KMX patch hash is `bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67`, with matching negative copy controls for each used fixed-value shape.

No ELF rebuild trigger fired. Inherited, not newly measured, pins remain:

- Default: `f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4`.
- Devnet: `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`.
- Pool: `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`.

Headline: `AspisR1.RPx_Deployed.deployed`; adopted frozen3 and two-transaction game remain. L154 is a statement parameter. P6/D188 option-A native contract semantic transport is retained/reclassified, never removed. Root carrier/ABI, source-to-ELF, compiler/library/Aeneas interpretation, runtime digest=H and RuntimePersistence remain. RuntimeReturnData and RuntimeMemcmp are accepted trust rows per owner 2026-11-04; NFK's historical pending wording is superseded, not discharged. No soundness metric, privacy condition, protocol parameter, bound or two-transaction assumption changed. These are bounded native checks and symbolic/model theorems, not a cryptographic security or cost conclusion.

## Budget, resources and continuation

All **60 Kani, 50 Lean/support, 3 extraction** slots are charged. Submitted: 59/48/3; K001/L009/L014 failed before launch and are conservatively charged. Negative controls intentionally exit 1; failed elaborations and E002 are excluded, with source corrections recorded. No timeout, memory kill, cap raise, unchanged failed prover rerun, transport-255 event or extra extraction. `NFQ_ATTEMPTS.jsonl` includes full per-target source/exit/time/RSS/swap/axioms receipts; `NFQ_ATTEMPTS_INDEX.json` reconciles every slot. Peak reported RSS: **5,731,464 KiB**, swap0. All scopes use MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64 after allowed:true AND exit0 admission. Lean uses -M7000; Rust opt3; maximum one own scope at once.

`NFQ_REMAINING.json`/`.md` list every remaining **279 functions / 322 rows**, exact callee packets, domains, certificate shape and missing native obligation. Priority is prepare -> Prepared::new / powers / verify_observed -> query_loop -> checkpoint. Bottom-up independent members need not wait on query_loop. Do not rerun completed gates without a source/environment/evidence change; this job has no prover budget left.

Private host workspace: `/home/dombarker/project-offloads/codex-cx-slice-d-define-20261104`. Private cache: `/home/dombarker/project-offloads/codex-cx-slice-d-define-cache-20261104`. All 31 own objects are copied into its `NFQ_exports_20261104`; exact hashes are in `NFQ_CACHE_END.json`. Imported cache hashes are stored once as `NFQ_CACHE_IMPORTS.json.xz` plus its raw sha256. Resolve libraries using the pinned receipt LEAN_PATH; do not substitute old FIo/S1 imports (the rejected attempts show the duplicate-Phase failure). Own Rust targets were removed after all gates; source, LLBC, audit C/binaries, receipts, objects and all caches remain. No cache deletion. No file exceeds 20 MB and no __pycache__ is committed. Preserved raw logs/snapshots/patches carry whitespace; authored source/docs pass whitespace checks.

Stage commits: `fb5fd5191bd` definition; `5e546d45136` order; `ebd3ef94e23` first five; `2c9216466dd` union correction; `e86a8d76f91` eleven more plus final model audit. The final handoff/validation commit follows; no push.
