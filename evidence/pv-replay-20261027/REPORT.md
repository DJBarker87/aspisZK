# Private research headline replay: complete

**Target not yet established. Zero premises removed, added or changed.** This is a dry coherence replay, not a deployed privacy or final-release proof.

Branch `codex/pv-replay-20261027`, base `cc82f1f8677e62fde0a4fad75fe09eb48db8e8d6`. Sources pinned to research `b90540e01c10a102535dcc0c0b0c50fb18880e0f`. Private host root `/home/dombarker/project-offloads/codex-pv-replay-20261027/`. Commits are local; no push. No existing project proof, Rust/program file, key, shared env-J source/object, launcher or environment was modified. The pre-existing staged C3-BIN change is untouched and excluded from commits.

## Closure and reuse

Both requested roots are covered; `PrivacyR1HeadlineV2` is already an ancestor of `PrivacyR1HeadlineDeployedReal`.

| Result | Count |
|---|---:|
| Project modules | 672 |
| Reused, exact source/dependency-object hashes | 537 |
| Successfully compiled project modules | 135 |
| Project proof failures | 0 |
| Actual loaded modules, including pinned libraries | 6,345 |
| External loaded objects, never rebuilt | 5,673 |

`replay-plan.tsv` is dependency-first, with rebuild-authoritative research source paths, source SHA256 and actual dependency-object fingerprints. `replay-plan.json` retains historical source resolutions and recursive source/import fingerprints. `actual-import-dag.{json,tsv}` records Lean's loaded graph, including implicit/library imports. Every project module is present; its direct imports agree with the source plan after accounting for implicit Init. There are **no PV_* project modules in this headline's import closure**; unrelated native-proof publications are not promoted into this replay.

Every reuse in `receipts/results.jsonl` cites a successful prior receipt and exact matching source/dependency/output hashes. The three shared-source cohort differences are recorded with both hashes in `shared-source-differences.json`; SOURCE-COHORT.md names the required declarations. They were compiled privately, never overwritten in shared storage.

## Compiles, failures and resource evidence

**179/600** charged Lean compiles, IDs **28000–28178**: 135 project successes, one successful final diagnostic, 41 early loader failures, two failed diagnostic helpers. **421 compiles unused** because the assigned closure and audit are complete. Kani/Rust/SBF/Mathlib/Aeneas builds: **0**.

All attempts run one scope at a time with MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64, Lean -M7000; no cap raised. Peak RSS across all attempts **4,308,768 KiB**, swaps **0**. Per-attempt target, exact command, exit, GNU and outer wall times, RSS, swaps, source revision/SHA, dependency hashes, full axiom output and errors are in `receipts/receipt-*.json`, with raw `out-*`, `time-*` and admission/launcher logs. The only five successful source modules without original axiom prints are generated Types/Funs/FunsExternal definition modules, recorded as such; all theorem-source compiles retain their original print results.

Retained failures, with exact complete errors in `failures.json` and the raw logs:

- 28000–28020: missing `Init.olean.server` in the initial private loader mirror.
- 28021–28038: `missing IR data file for module Init.Prelude`; 28039: `missing data file for module Init.Data.Fin.Bitwise`; 28040: missing `AeneasMeta.Extensions` object in the effective namespace. The replacement loader includes pinned companions, follows namespace symlinks and records the loader binding in the input fingerprint. Source unchanged; no unchanged memory/resource failure retried. Both environmental generations remain recorded.
- 28176/28177: diagnostics rejected bindings using imported reserved token `name`; first helper also reports unknown pair-projection types. Both source files and failures are retained. A separate diagnostic uses `declName`; no project proof was repaired or suppressed.

## Final axioms audit

**28178 / PV_ReplayAudit3**, exit **0**, GNU wall **1:07.99**, peak RSS **4,265,412 KiB**, swaps **0**. Its source revision is recorded in `audit-revision.txt` and the receipt; closure source revision remains research b90540e01c. It executes `#print axioms` for **3,905 distinct theorems** in every imported R1Z/PV module, including private/generated theorem declarations, plus three explicit endpoint prints (3,908 printed results).

The complete axiom union is exactly **{propext, Classical.choice, Quot.sound}**. **Other axioms with defining module: none.** Both `privacy_headline_v2` alternatives and `privacy_headline_deployed` print only those three accepted axioms. Machine-readable results: `axioms-audit.json`; complete transcript: `receipts/out-28178.log`. The diagnostic adds no theorem or axiom. No unchanged full replay was repeated.

Final source/object and direct-external-pin integrity passes: `receipts/final-integrity.json`. Full loaded external object SHA256/size/path pins: `receipts/external-object-manifest.json`. An initial read-only integrity checker incorrectly required Std objects to exist in the private mirror; `initial-integrity-mirror-only.json` retains those false missing-object reports. Correct resolution includes the pinned external LEAN_PATH, exactly as Lean did. No objects or compiles were changed for this reporting correction. The large redundant loader-binding listing stays on the host with SHA256 and size recorded in final integrity evidence.

## Retained premises and next deliverable

PREMISES.md gives the binder inventory and before/after zero delta. DeployedReal still assumes **RustRealRefinement**: a concrete nonempty shared RunJoin with exact runtime/model marginals and complete view-plus-observer-decision agreement outside the fixed parser/seed/fuel bad event, for every matching adversary/witness. It still takes free runtime/observer parameters. V2 retains BuilderPremises, CallerLaw (or explicit fibre/exhaustion laws), real builder/checker/retry join and ideal simulator join.

Deployment obligations remain: prover proved=shipped; E1/E2; actual native Records/compiler/snapshot and RunJoin association; OS-failure witness-independence under option B; inversion boundary linkage; complete L1/L2/L3 side channels/compiler preservation; client proof-account-route binding; artifact adoption and final frozen release replay. T stays capped to entropy_law, entropy_kernel, observation; V371 remains substantive trust. No trust expansion, observer/simulator weakening, or security-target change.

Next concrete deliverable: the lead selects this exact source/dependency cohort for integration, then connects the remaining deployed native execution obligations to the endpoint and performs the final release closure replay/audit against the final adopted artifacts. The private source/object cache is retained for that reuse. This dry replay stops because its closure and requested audit are complete, not because the privacy target is established.
