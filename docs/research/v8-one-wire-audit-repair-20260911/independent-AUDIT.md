# Aspis V8 — independent source and proof-boundary audit

Audit date: 11 September 2026.

Repository: `DJBarker87/aspisZK`.

Pinned V8 head: `30a303a344dbb42e24ad8f42a8804819747942bc`.

Previous reviewed checkpoint: `531b50ed6cd06d5902417edf614daee137c19acb`.

Main/V7 head observed: `620be11122cb9abd72f7b3238e257becf853e13a` (unchanged).

## Executive verdict

The newest V8 commit contains genuine deterministic proof work. In the source inspected, I did not find an obvious `sorry`, added axiom, kernel-bypass command, or definition that simply declares the requested security conclusion true. The authenticated-opening chain is not merely assuming its conclusion: it constructs sibling paths and fixed-word opening equalities from a functional verification algorithm.

However, this is **not a whole-repository clean bill of health**, not an independently repeated Lean build, and not a global 100-bit security certification. I found a concrete remaining **one-wire coherence gap** in the headline composition, together with unresolved timing/probability and extraction interfaces. These are specification/integration limitations, not an exhibited forgery or a demonstrated false Lean theorem.

Recommendation: retain the work, but do not promote the headline result to “compiled selected verifier success implies fully authenticated ideal acceptance” until its inputs are constructed from the same literal execution. Perform an independent clean first-party rebuild and kernel replay before trusting the experiment's cached artifacts as release evidence.

## What changed

Commit `30a303a` is titled `research(v8): construct ideal execution from selected wire run`, timestamped 2026-09-11 18:34:59 UTC (19:34:59 BST).

The new chain adds exact Wire projections, a functional model of the paired minimal-Merkle verifier, a C2 prefix-word authentication alternative, and composition into the existing ideal-execution endpoint. The reported proof-body maximum is unchanged at **40,282 bytes**. The commit reports no new CU or prover-time benchmark. Main remains unchanged at `620be111`.

This improves on `531b50ed`, which started at a parsed field-level `Program`/`SuccessfulAt` boundary. It does not complete all lower source bindings or global probability composition.

## Audit scope and limitations

I inspected all **11 new/modified Lean modules in the latest commit**, and six critical preceding modules used in the field-level and residual-recovery chain. I also compared the functional Merkle model with `crates/aspis-core/src/v7_merkle208.rs`, inspected the recorded build log and the evidence-audit script, and ran independent Python diagnostics.

The 11 current modules, under `docs/research/v8-no-work-100-20260907/experiments/`, were:

1. `AuthenticatedPhaseWords.lean`
2. `FixedWordQueryTerminal.lean`
3. `PrefixPackedQueryBatch.lean`
4. `RustShapedMinimalMultiproof.lean`
5. `SelectedAuthenticatedSuccessfulRun.lean`
6. `SelectedMultiproofOpeningEquality.lean`
7. `SelectedMultiproofPrefixProjection.lean`
8. `SelectedWireBytes.lean`
9. `SelectedWireMerkleRun.lean`
10. `SelectedWireOpeningTerminal.lean`
11. `SuccessfulCompleteSelectedWire.lean`

The six preceding modules inspected were:

- `SuccessfulSelectedVerifierRun.lean`
- `MinimalMultiproofPaths.lean`
- `SelectedResidualPrefixClassification.lean`
- `SelectedResidualRecoveryBound.lean`
- `SelectedResidualHighRecovery.lean`
- `SelectedMiddleImageRecovery.lean`

This does not constitute an audit of every historical V8 experiment or every transitive imported theorem. The repository metadata does not establish which individual edits were authored by Luna. The audit concerns their content, not the model label.

I could read the pinned source and evidence via the connected GitHub tools. The execution environment did not have `lean` or `lake`, and a direct GitHub clone failed because the execution environment could not resolve the host. Therefore I did **not** independently compile these modules, inspect the ignored binary `.olean` outputs, run SBF, or replay all imported declarations. Statements about recorded green Lean runs below are explicitly attributed to the committed evidence.

## Finding 1 — The headline still does not enforce one-wire coherence

**Severity: high for a claim of full source closure; not evidence of an exploitable verifier defect.**

The theorem

`SuccessfulCompleteSelectedWire.successful_complete_selected_wire_constructs_ideal_execution_or_auth_failure`

takes both an independent `p : Program 22` and a `body : List Byte`.

The `merkle : SuccessfulMerkleRun ... body` input ties the roots, records and frontiers to a parsed Wire. Separately, `PathChecks`, `fields`, and the scalar `terminal` premise are built using `p.bodies`, `p.data`, `p.weights`, `p.claims`, and `p.inactive`.

There is an explicit `rootBound` equality, but no corresponding equality tying `merkle.wire.values` to the fixed-field projections consumed by `p.bodies`/`p.data`/`p.claims`. The theorem's output is `SuccessfulAt (phaseProgram p ...)` and ideal acceptance for that program. It is not yet acceptance for a program constructed from the supplied `body` and literal verifier transcript.

A useful mutation test is to alter a canonical fixed field in `body`, leaving its roots, records and frontiers unchanged. The parsed Wire's `values` change. All Merkle-visible projections remain identical. The separately supplied `p` need not change. Our Python byte-parser diagnostic confirms this separation at the representation boundary.

**This is not a complete accepting-proof counterexample.** It demonstrates that the theorem interface does not, by itself, rule out mixing the Merkle part of one body with semantic/response data from another program. The conditional theorem can remain perfectly correct under its existing hypotheses.

### Required repair

Construct the relevant `Program` from the same body and actual causal execution, or supply and then derive explicit coherence facts for every consumed projection:

- fixed values and component claims;
- OOD values and challenge-derived geometry;
- response0, final256 and each later response;
- both roots, records and frontier halves;
- public statement, runtime context and transcript framing.

For earlier response boundaries, require equality of the already-consumed/committed portions on the realised execution. Do not incorrectly demand that an earlier prover callback already know the entire eventual proof body.

The final source theorem must derive these facts from genuine verifier execution, not merely move them into a new `CoherentProgram` structure that is still externally supplied.

## Finding 2 — The phase-prefix facts do not yet establish chronology

**Severity: material cryptographic integration obligation.**

The authentication chain accepts `c1Prefix`, `c2Prefix`, `fullLog`, answer consistency, and `TraceIncludedInLog` premises. The source itself explicitly notes that inclusion does not prove prefix nesting or timing.

The deterministic theorem appropriately produces:

- correct fixed-word projection; or
- a C1 late-target hit; or
- a C2 late-target hit; or
- a shared raw truncated-hash collision.

This is useful and not circular. But the data must eventually be constructed at the actual protocol cuts: C1 before the appropriate later challenges, C2 at its later commitment cut, and both before the challenges that need them fixed. Set/list membership in a supplied log alone does not establish those temporal properties.

The new theorem does not bound the authentication alternatives, count actual adversary/oracle queries, or show Fiat–Shamir freshness. These remain separate, necessary proof obligations.

### Required repair

Derive the two prefixes and their cutoffs from one literal execution, then connect the same full hash-call log to the shared collision/late-target probability bounds. Preserve aborts, cached calls, adversarial scheduling, and the actual resource budget.

## Finding 3 — Algebraic `RecoveredHigh` is not yet a checked payment extractor

**Severity: high if the conditional residual estimate is presented as global soundness.**

`SelectedResidualHighRecovery.RecoveredHigh` genuinely requires the same quotient `Q` to carry the high-prefix witness, support condition and recovered representation. It is not defined as “any case we choose to call successful.”

Unfolding the underlying `Recovered` predicate shows an existential tuple in a fixed finite family, a minimum own-symbol support count, a batching/reconstruction identity, and C1 membership in the early family. These are concrete algebraic properties.

Nevertheless, that is not the same proposition as:

> A resource-bounded extractor, using only permitted access, returns a witness accepted by the payment compiler/validator for this public statement and runtime state.

`SelectedResidualRecoveryBound` bounds the residual after removing `RecoveredHigh`. That removal is legitimate for that explicitly defined algebraic event. Turning it into a bound on accepted-but-unextractable payments still needs the extractor/payment bridge and the other accepted branches and failure charges.

### Required repair

Keep `RecoveredHigh`, executable decoding success, complete checked payment validity, and global argument-of-knowledge failure as separate predicates. Prove their links; never silently rename the first as the last.

## Finding 4 — Cached `.olean` evidence is not a clean dependency replay

**Severity: unresolved assurance/reproducibility requirement, not evidence of tampering.**

The committed `successful-complete-selected-wire-v2.log` records Lean 4.32.0, exit zero, matching source/output hashes, standard-only transitive axioms for the headline theorem, and 1,111 unchanged provenance entries. This is considerably better evidence than an unsupported “green” message.

The same log explicitly says:

`NATIVE_PACKAGE_CACHE_BOUNDARY=pinned revisions; not a replay of package compilation`

The authentication review also records copy-only imported artifacts and an incompatible native source variant that was deliberately not substituted. That may be a sensible working setup, but it means an independent reviewer still needs the exact source/version/artifact graph, not just the current checkout plus a claim that all dependencies were compiled.

The inspected Python evidence auditor checks source/log/manifest hashes, recorded axiom strings, settings and optional local output hashes. It does not rerun Lean, rebuild imports, or validate theorem meanings.

### Required repair

In a clean isolated checkout with no production secrets:

1. Pin Lean and every first-party and third-party source revision.
2. Rebuild first-party dependencies from the exact claimed source variants.
3. Reject missing source-to-artifact mappings or accidental namespace/version substitutions.
4. Print the full public theorem signatures, not only their axiom lists.
5. Run the appropriate independent kernel replay, such as `lean4checker --fresh`, using a compatible pinned setup.
6. Compare the resulting theorem against a separately authored, frozen intended statement.

Ordinary build success, axiom hygiene, kernel replay, source correspondence and statement adequacy are distinct assurance layers.

## Positive findings

### The functional Merkle result is substantive

`RustShapedMinimalMultiproof.verify` actually checks guards, consumes entries/frontier nodes, executes the level walk, checks exact frontier exhaustion and checks both final roots. `pass_sound`, `levels_sound` and `verify_selected_accepted` derive the inductive execution certificate; the verifier does not accept that certificate as input.

`MinimalMultiproofPaths.accepted_q22_paths` then reconstructs sibling paths for each original query ordinal. This is not `Accepted := CorrectOpening` disguised as a theorem.

The pure model uses natural numbers and lists rather than compiled `u32`/mutable-Vec code. That last refinement still matters, but the model is concrete enough to test and compare.

### Opening equality is actually discharged in the newest chain

`FixedWordQueryTerminal.acceptance_fixed` has an `OpeningEquality` premise. That is a strong interface if viewed in isolation.

The new chain constructs it:

functional multiproof success -> paths -> phase-prefix projection or explicit failure -> canonical packed-record values -> exact fixed-word opening equality -> terminal equivalence.

Thus this particular assumption is not merely renamed and abandoned at the latest endpoint.

### Canonical parsing is not bypassed with a fallback

The source uses totalised `getD`/`Option.getD` to define values on all inputs, but successful-path lemmas retain actual parsing premises and establish lengths and bounds. The inspected new authentication consumers preserve the canonical query-record parser premise. I found no basis here for saying malformed queried limbs have been defined into validity.

### Classifier premises have real producers

`SelectedResidualRecoveryBound` accepts a `CandidateClassifies` premise. `SelectedResidualPrefixClassification.exists_source_classifier` constructs a classifier from earlier parent/classification theorems.

Its important quantifier order is visibly:

`exists E ... forall OOD data, exists beta ... forall later gamma/candidate ...`

rather than choosing the exceptional polynomial after the offending gamma. This passes the immediate circularity/quantifier-order check. It does not independently certify every underlying imported algebraic theorem.

### `rfl` and `noncomputable` are not evidence of cheating

Many new lemmas identify constructor projections or equivalent wrappers and appropriately use reflexivity. They should not be counted as new cryptographic security arguments, but there is nothing improper about them.

Likewise, noncomputable finite-family selection is legitimate mathematics. It does not itself supply an efficient extraction algorithm; that is the separate boundary described above.

## Independent diagnostics actually run

`audit_checks.py` contains two separately structured Python transcriptions of the inspected imperative and functional Merkle loops, using SHA-256 truncated to 26 bytes. These are **not actual Lean or Rust/SBF executions**.

Results:

- 17,845 comparisons;
- 2,275 valid fixtures, including all nonempty query subsets for depths 0–3 and 2,000 seeded random fixtures through depth 18;
- 15,570 malformed/mutated cases;
- zero mismatches;
- an explicit depth-18/q22 fixture attaining frontier 296;
- exact body census 40,282 bytes;
- a canonical fixed-field mutation preserves Merkle-visible byte projections while changing the parsed values.

The parser mutation fixture does not claim to be a complete authenticated payment proof. It isolates the byte-interface issue; the theorem-signature analysis establishes the missing cross-interface equality.

## Independent numerical correction

The currently recorded combined pair-root degree cap is 90,407,376. With

`N = (2^31 - 1)^4 - (2^31 - 1)^2`,

the expression

`90,407,376 * 90,407,375 / (N * (N - 1))`

has approximately **195.1401 bits**, not the approximately 214-bit figure mentioned in earlier conversational summaries for smaller root sets. This remains far below a 100-bit error budget. It is an arithmetic correction to the summary, not a demonstrated defect in Lean or a new global security result.

## Release decision

**Keep the work. Do not call it fully source-connected or globally 100-bit secure yet.**

Before the next “closure” claim, require:

- one-body/program coherence;
- literal compiled-success -> functional-run construction;
- causal prefix and challenge-law construction;
- numerical charging of the actual authentication/Fiat–Shamir events;
- algebraic recovery -> allowed resource-bounded checked payment extraction;
- independent source/artifact rebuild and kernel replay;
- separate full-view zero-knowledge closure.

Do not replace these with another structure whose fields assert the desired conclusions.

## Evidence locations

All repository references below are pinned to the V8 audit head above.

- All 17 Lean modules listed in the scope section.
- `crates/aspis-core/src/v7_merkle208.rs`.
- `docs/research/v8-no-work-100-20260907/selected-wire-opening-execution-review.md`.
- `docs/research/v8-no-work-100-20260907/authenticated-phase-words-review.md` (also retained in the commit diff).
- `docs/research/v8-no-work-100-20260907/experiments/successful-complete-selected-wire-v2.log`.
- `docs/research/v8-no-work-100-20260907/experiments/audit_selected_authenticated_successful_run.py`.
- Official Lean reference: “Validating a Lean Proof”, including printing axioms, `lean4checker --fresh`, and trusted-statement comparison. Consult the version applicable to the pinned toolchain.

The accompanying `results.json` is generated by the independent diagnostic script, not copied from the repository's benchmark or Lean logs.
