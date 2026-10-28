# Runjoin24 — LOG D331 resume

Target not yet established. Entry HEAD b83409d44f64d4604683c0384c077d95638211a3; worktree /Users/dominic/ZK/.worktrees/pv-runjoin; branch codex/pv-runjoin-20261026.

**Stopped on a checked counterexample to universal raw-family V153.** No endpoint or shipped implementation change was applied.

## Exact statement boundary

`BuilderSource.SourceIdentification source toInstance` has three fields, for fixed `source : HonestProver K` and fixed `toInstance : source.Instance → BuilderCanonical.Instance`:

```lean
public_eq : ∀ w : source.Instance,
  source.public w = BuilderSource.prover.public (toInstance w)
build_eq : ∀ w : source.Instance,
  source.build w = BuilderSource.prover.build (toInstance w)
transport_eq : source.transport = BuilderSource.π
```

The endpoint `PrivacyR1HeadlineDeployedReal.privacy_headline_deployed` has **no SourceIdentification argument**. It fixes `input := BuilderSource.prover` and takes `RustRealRefinement template outputs x rust observer_program`. The existing checked exact print is evidence/pv-runjoin20-20261027/out-37099.log. SourceIdentification is a separate source handoff used by `builder_refinement_D46_D51`; claiming the endpoint itself is vacuous from its failure would misstate its checked type.

The native diagnostic source is `PV_Src_NativeIdentification.prover inputs transport`:

```lean
Instance := I
public i := mapPub (BuilderPublicProjection.semanticPublic
  (PV_Src_Public.output (publicInput (inputs i))))
build i := columns PV_Src_Forest_Columns.read (inputs i).compiled.semantic_c1.c1
transport := transport
```

Thus `public` DOES read cached `compiled.public_statement` through `publicInput`; `build` DOES read cached `semantic_c1.c1`, but reads neither cached `trace.variant` nor cached `trace` at all. Its name does not establish an actual compiler-return association.

The canonical carrier is
`{p : Public F × Wspend // RspendPlus (mapPub p.1) (BuilderCanonical.liftWitness p.2)}`.
The canonical public is `mapPub p.val.1`; canonical build is
`BuilderRefinement.mergedTrace (rustWitness p.val.2) (rustPublic p.val.1)`;
`BuilderCanonical.canonical_trace` identifies that merged trace with
`buildModel (mapPub p.val.1) (modelWitness (liftWitness p.val.2))`.
`BuilderSource.π := AspisR1.rowEquiv`.

`UniversalBuild22.toInstance inputs admitted i` uses the canonical public of `publicInput (inputs i)` and the witness reconstructed from `records (inputs i)`, with `admitted i` as its subtype proof. There is no such map on all raw Input: runjoin23 checked that semantic admission is false on its non-conserving `bad`. Failure to construct that map is not alone a proof that public projection is false.

## Truth values and decisive counterexample

**(b) Non-conserving raw input:** `PremiseTruth24.bad_public_projection` is TRUE (38124, reprinted/audited38194): source.public equals the canonical public projection for this raw data. The full `SourceIdentification.public_eq` is a statement about a *supplied* canonical `toInstance`; no raw record-based map exists here. `CanonicalMapBoundary24.bad_no_canonical_record` and `no_raw_record_map` (38127, audited38194) prove that no canonical instance has this input's reconstructed witness: its conservation would require 0=1+0. Thus the requested full field on `UniversalBuild22.toInstance bad` has no well-typed instance; it is not justified to mark that field TRUE or FALSE without a different specified map. `bad_public_eq_false_of_witness` records the conditional incompatibility with a record-preserving map, but its witness-association hypothesis is itself impossible, as the stronger boundary theorem shows; it is **not** an unconditional V152 counterexample. No arbitrary replacement map has been chosen.

**(c) Original altered trace.variant input:** `PremiseTruth24.variant_build_eq` and `variant_public_eq` are TRUE for the exact singleton record/public map using the checked admission proof (38124, audited38194). Changing cached trace.variant leaves semantic_c1.c1, public_statement, request, and records unchanged. `variant_build_preserved` and `variant_public_preserved` check this by definitional equality. V153 reads cached semantic columns; it does not read cached trace.variant. The prior universal compiler-return association is false, but these V152/V153 equations are true. `raw_transport_eq` is TRUE for all raw inputs, including both original counterexamples (38124/38194); it is a whole-equivalence equality, independent of cached fields.

**(d) Decisive V153 counterexample on another admitted raw instance:** `PaddingCounterexample24.bad` keeps the exact admitted transfer's request, witness, change, lane anchor, snapshot, cached public_statement, and cached trace. It replaces only cached semantic_c1.c1 by 16 short constant-one vectors. Its Admission and V152 at the exact singleton canonical map are checked. Its raw trace cell (column0,row13) is1; every canonical trace has0 there. The named `model_padding`/`canonical_padding` lemmas use the row13 padding branch and evaluate no hash, bank, or recurrence. Checked38126, reprinted and audited38195:

```lean
build_eq_false (w : BuilderCanonical.Instance (K := K)) :
  raw.build bad ≠ BuilderSource.prover.build w

universal_build_eq_false (f : Input → BuilderCanonical.Instance (K := K)) :
  ¬ (∀ i : Input, raw.build i = BuilderSource.prover.build (f i))

identification_unsatisfiable (f : Input → BuilderCanonical.Instance (K := K)) :
  ¬ BuilderSource.SourceIdentification raw f
```

`admitted_identification_unsatisfiable` proves the same failure for EVERY map from `{i : Input // Admission i}`. **Admission alone cannot repair this interface.** This is the requested checked counterexample to V153 interpreted as a universal equality for the raw native source family; universal work stopped at38126. It is a counterexample to the unrestricted cached source adapter, not a finding that the shipped compiler returns bad columns.

**Endpoint qualification:** this makes a theorem conditional on SourceIdentification of *that raw source* vacuous. It does **not** make the actual named endpoint vacuous: that endpoint does not have that premise or carrier. FinalAudit24 prints its exact type and proves `endpoint_input_is_canonical`; `canonical_identification` proves its existing fixed input satisfies SourceIdentification with the identity map. No raw-source refinement or privacy conclusion is obtained from this fact.

## Recommendation — proposed only, not applied

Owner should restrict the source handoff's quantified carrier to honest inputs carrying semantic Admission **and the full cached-payload association**
`run i = ok (.Ok i.compiled)` (both Result layers retained), or define the source payload from the successful returned compiler value rather than arbitrary cached data. Keep the same public projection and observer. Admission excludes the non-conserving raw input; full payload association excludes both cached mutations. Existing Checked/frontier guards in UniversalBuild22 remain explicit proof obligations; including them in a proposed carrier makes its existing identification theorem directly applicable. The two original fixture inputs already have checked Admission, compiler-return, Checked and canonical-frontier evidence, so this proposed guarded carrier is inhabited; this is not a new universal source closure. Establishing the minimum guards the actual deployed call enforces remains proof work. No source domain, endpoint statement, trust item, simulator, observer, shipped source or key was changed.

Owner's next deliverable: choose the intended honest source carrier/map and connect the actual deployed inputs to its successful returned payloads. Do not commission another raw-domain universal trace proof: the checked padding counterexample rules it out.


## Ledger, verification and receipts

Recount6 remains **407 rows; OPEN86; CLOSED-ON-CANDIDATE44** (400P,3T,4C). Whole rows removed0; V038/V045/V047/V152–V154 retained, with V153's unrestricted raw-family formulation now counterexampled. Deployed P OPEN→OPEN; constructed P and records2/8/6 unchanged. Quoting recount5's continuing boundary: “Deployed PV_Src_Premises remains five fields. No deployed source-identification closure is inferred.” Endpoint premises removed/added/weakened0/0/0. T remains exactly entropy_law, entropy_kernel, observation. No privacy-release claim.

10/80 Lean attempts charged,6 accepted,4 rejected;0Kani;0localLean;70 attempts remain.38122 was retired without submission by the unchanged-input wrapper while the retained cache overlay was still being created; its separate not-launched receipt records0 charge.38121 failed before importing the missing companion-cache object;38123 failed only to infer implicit public-family arguments;38125 failed on the field cast of1;38196 failed on the omitted local CharP instance. All failed sources/logs retained; each replacement changed source or the missing dependency view. No memory kill, timeout, reservation refusal, increased cap, full manifest replay or unchanged full regression.

Final audits used the requested38194–38196:38194 public/map and38195 counterexample pass.38196 printed the full endpoint and its standard axioms but rejected two new boundary lemmas for missing CharP; corrected FinalAudit24 passes38128 (next unused authorized ID, recorded supplemental final audit). All current6 source modules match accepted git/snapshot receipts. Accepted proof-stage HEAD45614680b3; evidence commit follows. `commits.txt` records the path-limited stage commits from entryb83409d44f.

All host scopes were sequential MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64, Lean-M7000. PeakRSS5,009,928,192bytes; every swap count0. Full target, exit, host wall time, RSS, swap, exact source revision/blob/sha256, dependency fingerprint, command and complete axioms appear in receipt-*.json, receipt-index.tsv and out-*.log/time-*.log. All accepted theorems use only propext, Classical.choice, Quot.sound (or a subset); the failed logs' sorryAx results are rejected and never credited.

Before the first host attempt,5673 external objects were checked against h4/SCOPE; the final actual private prefix also checks against all5673. The1354-project-module closure has no unpinned module (initial1353 plus new CanonicalMapBoundary24); EJR/freeze/h5' precedence and tracked conflicts are recorded in focused-resolution.json. Own corrected targets are pinned by git revision/blob/sha256 in own-source-refresh.json, final-source-refresh.json and each compile receipt. Retained private companion links changed no shared source. h6 replay reuse verifies669 reused roots and785 transitive source/object fingerprints, with no mismatch and unchanged toolchain; final source/object cache verification is recorded in focused-project-cache-check.json.

No push, merge, shipped-source, wallet/key, simulator, observer or trust change. No endpoint edit; owner recommendation remains prose only. Stop reason is the checked raw-carrier V153 counterexample, not budget exhaustion.
