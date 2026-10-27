# Shared extraction obstruction: decision packet (2026-10-27)

Status: unadopted proposal on `codex/pv-extract-20261027`, base `7599dff5b274d52324ae8681664f6b343f9a81ac`. No shipped source changes. Privacy target not yet established.

The recommended next step is a narrow D187 host-prover index-loop candidate for op223, with the existing shared implementation retained for the verifier. Do not disable the shared extractor preflight. Keep a separate, justified extractor repair track for shared loans and generic library functions; the diagnostic shows that deleting the guard is insufficient.

## Evidence and decision boundary

The inventory and exact root-cause/diagnostic tables are [INVENTORY](../evidence/pv-extract-20261027/INVENTORY.md) and [ROOT-CAUSE](../evidence/pv-extract-20261027/ROOT-CAUSE.md). Fifteen callback ops have recorded exact reference-output refusals. Op253 has an additional internal shared-loan failure, outside that syntactic guard. Several graphs also have independent Drop barriers.

Fresh Charon accepts shipped op223 under built and optimized MIR. Both Aeneas no-preflight diagnostics fail in `InterpReduceCollapse.ml:1991` while remapping shared-borrow abstraction IDs during loop-context matching; no Lean is emitted. The public compressor returns QM31 by value and owns no destructor-bearing object, but its iterator still creates internal shared loans. Neither a public value result nor successful Rust borrow checking repairs that invariant.

The index candidate passes pinned Charon and **the unchanged pinned Aeneas with the preflight enabled**. Its control extraction is definitionally equal to the P6 compressor, including the complete Result on arbitrary inputs, once its five field calls use the same explicit callback dictionary; see `R1Z.PV_Ext_IndexBridge.reference`, `loop_reference`, `body_reference` and receipt42408. This does not associate the shipped iterator function with the index candidate. A second extraction closes the index leaf's field arithmetic with zero opaque function declarations; its per-declaration Lean replay and comparison to retained current field source are recorded separately below.

## Route (i): repair extraction of shared slice iteration

Retain the fail-closed policy for unresolved mutable references and destructor semantics. A sound repair needs a function/graph-specific preflight classification, successful internal loan processing, typed emitted code, and a demonstrable source/result relation. A mere exception for “root returns QM31” would expose the downstream missing-map error found here.

The narrow shared-iterator work is to isolate the missing abstraction mapping in `collapse_ctx_following_sequence` and establish why every borrow sequence ID is either preserved, merged into a known new ID, or legitimately eliminated. The fix must follow that invariant. Do not replace failed lookups with arbitrary IDs, omit the loan sequence, erase Drop, handwrite an extraction body, or equate a fixture result with arbitrary-input source semantics.

Required diagnostic regressions: the op223 graph under both MIR selections; shared next/double-ended/chunks/enumerate cases used by op79/222/258; mutation/backward update and captured-loan cases only where the repaired class claims support. Generic-array, nested mutable ADTs and Drop are separate capabilities; an op223 fix must not certify them. Compile emitted Lean against Env-J's pinned backend, audit all generated definitions/bridges, retain original/new tool and input/output hashes, and make adoption of the repaired extractor explicit. No source changes or verifier ELF reruns are required merely for a source-preserving tool repair; coherent proof closure still is.

Benefit: one justified repair can unblock several exact shipped functions without candidate source changes. Cost/risk: the observed failure is in symbolic loan/context invariants, beyond a conservative front-end check; the larger library graphs have other unsupported constructs. This job has no accepted repair.

## Route (ii): prover-local copies under D187

The patch [route-ii-op223.patch](../evidence/pv-extract-20261027/route-ii-op223.patch) adds only a private module in `aspis-r1-cost-probe`, guarded by both `prover` and `r1p-check`, and redirects the existing host `copy_endpoint_values` compressor call. The module initializes the same two values, visits `values[0]` through `values[len-1]` in order, performs add/mul_m31/mul in the same order (including the final power update), and returns the owned accumulator. Index increment wraps explicitly; with `i < len` and a valid usize length, no wrap occurs before the exit test. Empty input and all raw limb values remain in the function domain.

Only the patch is committed, under evidence; it has not been applied to `crates/`. A standalone probe in the assigned host directory checks extraction feasibility, not an applied candidate or adopted native implementation. `git apply --check` checks patch applicability without mutation. The patch is deliberately limited to op223's actual host caller, not a speculative replacement of the entire shared/library surface.

The affected functions need distinct treatment; replacing every library call with an index loop is not a single solution:

| Row/op | Candidate prover-local work | Shared/verifier implementation retained |
|---|---|---|
|V240/223|`compress_tagged_tuple` index fold; prepared patch|aspis-statement logup.rs:75 and every statement/program caller|
|V201/79|`eval_message` plus `eval_pair`, explicit paired indices and proof of q length/basis order|aspis-core r0/encoder.rs:10,28; basis::values unchanged|
|V228/132, V229/133|forest schedule builder/endpoint_counts and active-row/mask-cell enumeration, owned indexing; preserve sort/dedup/error order and registry contents|aspis-statement pool_v1/pair_forest_hiding.rs:101,120,179,233|
|V239/222|`multilinear_evaluate_qm31` plus `sparse_eq_weights`, explicit trailing-Boolean scan/suffix/prefix iteration; preserve allocation/bounds/errors|aspis-statement constraints_v4.rs:601,782|
|V241/224|host copy-helper wrapper plus its rows/logup producers; copying only the tiny wrapper leaves opaque calls and Drop obligations|aspis-statement pool_v1/pair_forest_semantic_oracle.rs:171 and logup/trace callees|
|V256/249|`gamma_sample`, `low_base_p_digits`, `add_small_base_p` (already host-prover code); rewrite mutable iterator in place only on the future candidate branch, preserve division/carry/order|shared aspis-core scalar sampler and verifier paths unchanged; no shared sampler replacement here|
|V264/258|`all_slots_clear` explicit row/side/value loops (already private host CT module); retain eager bitwise conjunction, masks read and all bounds failures, including oversized input after false|verifier path and public shared field methods unchanged|
|V260/253 (separate loan failure)|owned `Weights::raw` tensor/extra selection or extraction fission; indexing alone does not repair callback captures/shared-loan cleanup|shared public verifier interpretation and layout unchanged|
|V231/205|prover-local SHA core finalization/padding/output packing would need a complete digest-owned design, not just iteration rewriting|sha2-0.10.9 core_api.rs:60|
|V234/212|prover-local concrete digest finalization with explicit ownership/cleanup|digest-0.10.7 digest.rs:85|
|V235/215, V236/216|concrete host digest buffer/update/finalize, including partial-block buffering and all error/cleanup behavior|digest-0.10.7 core_api/wrapper.rs:148,170|
|V237/217|concrete owned digest initialization; broad generic-array inclusion is the observed obstruction, not default's return type|derived CoreWrapper Default, wrapper.rs:23|
|V238/219|concrete variable-core truncation/copy logic plus output-size behavior|digest-0.10.7 core_api/ct_variable.rs:114|
|V187/36 reference probes|concrete ownership-preserving Vec→Array adapter; preserve Err(Vec) ownership and cleanup; a borrowed copy helper is insufficient for the generic row|alloc generic Vec→Array conversion untouched|

`translate_aux_tuple` (pair_forest_trace.rs:522) is a further support helper: a future prover-local copy must rewrite its mutable limb iteration while preserving all cell/bank metadata. It is not a separate callback row. The proposed wider copies above are design work only; this patch implements the narrow compressor candidate. Third-party generic digest/alloc rows retain their actual generic quantifiers; a concrete host copy cannot discharge an unrestricted generic row by silently specializing its statement.

### Why verifier code paths keep the original

The proposed file and callsite lie solely in `crates/aspis-r1-cost-probe`. The only redirect is `host_semantic::copy_endpoint_values` at :423, already behind `r1p-check` in a module compiled only with `prover`. The new module requires both features. No Cargo feature, dependency, `aspis-core`, `aspis-statement`, or `programs/` file is modified by the patch. Existing statement paths—logup, direct range, state-only semantic, atomic registry, constraints and pool traces—continue to call the original shared compressor. The patch contains no global symbol override. Source reachability therefore preserves the verifier's implementation selection. **Byte identity remains a gate to measure**, not an ELF claim inferred solely from the source argument.

### Candidate gates to rerun before adoption

1. Apply only on a D187 candidate branch. Record final revision, feature matrix and lock/tool pins; extract the actual called host function and consumers, prove complete-Result arithmetic/caller transport, audit source-to-extraction receipts and standard axioms. Existing V164's unrestricted source premise is not removed by a canonical16 fixture or the unadopted probe.
2. Rebuild all three verifier ELFs after the final candidate source and confirm default `f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4`, devnet `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`, Pool `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`. If any differs, stop adoption and escalate the concrete byte change. No such rebuild is needed for this unapplied evidence patch.
3. Identical coins, byte-identical proofs on all pinned fixtures, with public outputs/failure paths/ledger/events included. Then at least **1,000 whole-prover paired differential runs**, not only compressor samples.
4. Quiet-host timing: median prover time **under15s** and **at most10% slowdown** against the frozen intended CT candidate, as required by D187/D191 adoption gates. Reserve a quiet window; capture workload, pair order, repetitions, caps and receipts. No timing conclusion comes from these extraction runs.
5. Revisit affected dependency closure, source/ELF association, E1/E2, real RunJoin, OS failure independence, client proof-account path, and L1/L2/L3 observables; do not add them to the three-field trust list. Field arithmetic uses Lean extraction, **zero Kani** under ruling(k). Control/index bounds may use future separately authorized gates, but no new Kani allocation is inferred here.

## Recommendation and next deliverable

Advance the narrow op223 host-only patch to the existing D187 candidate workflow after lead review; retain the shared source and pinned fail-closed tool. Its unchanged-tool extraction and P6 control equality make it the smallest demonstrated feasible source shape. The next concrete deliverable is an actual applied-candidate extraction receipt and complete field/caller/source binding followed by the fixture, 1,000-pair, ELF-pin and timing gates above. In parallel in the project plan, pursue a justified shared-loan context fix for route(i); do not assign more identical guarded op223 or SAT-hard Kani attempts.

No endpoint premise is removed by this packet. `PV_Ext_Op223Source.op223_source` is absent; V240 and V164 P_source_p6 remain open for the shipped implementation. The patch, index-leaf proofs and closed-field replay are evidence for a proposal, not source adoption or a privacy conclusion.

## Focused proof validation and limitations

The fresh closed index extraction emits23 functions plus3 constants, zero opaque functions, and no external-function template. All26 declarations type-check individually against the pinned Env-J backend (42410–42435); their Result constructors and arbitrary raw inputs are retained. `closed-split.json` pins the emitted blocks, import/type-carrier relocation and the narrow backend literal/API adaptations. This is a candidate extraction, not the shipped iterator.

Seventeen fresh constant/field dependency equalities through CM31.mul are proved against `ProverRwP7CurrentFieldSource`, by symbolic predecessor rewrites, with standard axioms. Remaining comparisons (CM31.mul_m31, mul_by_r, QM31 construction/add/mul/scale) are unsubmitted drafts under evidence, not published source laws. One direct complex-multiplication equality attempt hit the default heartbeat limit; replacing arithmetic unfolding with predecessor rewrites passed (42458,1.60s/4300460KiB/swap0). No cap or heartbeat limit was raised. The final corrected closed-candidate/P6 binding and closure audit consume the last compile slot; its receipt is authoritative for whether that final statement passed.

Final result: **60/60 Lean attempts exhausted (54pass,6fail), Kani0/0**. Final target `R1Z/PV_Ext_ClosedCandidate`, Env-J42460, compiled revision `5900139500b1fc0240ef3f9cc561c078411b7557`, **exit0,1.77s,4305060KiB GNU peak RSS,swap0**,47 accepted axiom outputs, all within propext/Classical.choice/Quot.sound. Its `candidate_reference` equation holds for arbitrary inputs and the entire Result, using the fresh closed field dependencies. One prior candidate compile failed due to record-field layout; final source corrected it. The only complete final bundle replay is42460. See [FINAL.json](../evidence/pv-extract-20261027/FINAL.json) for every target, source/dependency hash, revision, status, wall/RSS/swap and axiom result. ID42439 consumed no compile; next unused42461. No further compile budget remains.
