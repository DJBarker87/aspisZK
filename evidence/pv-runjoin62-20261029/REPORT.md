# Runjoin62 — target not established

Entry: `474daaf0f1857fc01175426409f88c098716f659` (LOG D507).
Exact worktree: `/Users/dominic/ZK/.worktrees/pv-runjoin`.
Branch: `codex/pv-runjoin-20261026`. Budget exhausted: **100 Lean attempts,
IDs 70600–70699, 0 Kani**. Audits used only 70697–70699.

## Adopted correction and residual audit

This is a **dictionary binding**, not a link restatement. `NativeResidual62`
composes existing installations onto residual `ops`; `NativeActual62.P`,
`runs` and `Links` specialize the existing ActualRun/Produced families to
`opsNative`. The nine link bodies, Produced, CaptureFactorSource60 and
CapturedTransport60 are unchanged. `boundaries.json` records hashes and the
empty protected-path diff. No ledger or protected owner file was edited.

V265 is bound through existing `CircleSelected.native_source` and the existing
`CircleOwnedSelected52.source` equality to the neutral callback. The new
`CircleBinding62.native_binding` composes those equalities on the owned side;
no colliding Types modules are co-imported. Both rows and the complete Result
behaviour are retained. **V265 inherits its structural source qualification;
this is not a machine proof that shipped code equals reference.** See
DICTIONARY-BINDING.md. Extraction/native fidelity, V370 and D381/D386 remain.

`residual-ops.json` is the reproducible declaration-graph audit: 98 syntactically
reachable prefix callbacks, conservatively including branches. Before the
correction, 16 reached fields came from arbitrary `ops`. Existing candidate
installations now bind op79/V201, op117/V217, op121/V220, op133/V229,
op134/V230, op222/V239, op226/V243, op229/V246, op230/V247 and op259/V265.
Existing op78/V200 and op231/V248 values are also installed, without restoring
their REDUCED ledger credit. The logging value op247/V255 likewise remains
REDUCED. The existing closed op254/V261 package is selected explicitly.
Each audit record names status, installation theorem and source evidence.

The arbitrary prefix fields left after binding are:

| Field | Row | Remaining obligation |
| --- | --- | --- |
| op32 | V183 | World-indexed allocator package; generic dictionary not fixed by a full closed row |
| op132 | V228 OPEN | Apply-masks success/native association; reference-only selector is not installed |
| op227 | V244 OPEN | Native terminal source/value association and success |
| op257 | V263 OPEN | Worker scheduling, effects and native association |

Publication additionally retains op4/V170's scoped drop obligation and
op232/V249 OPEN. Dynamic supplied store/hash callbacks and effect obligations
remain explicit. The audit is conservative static reachability, not a machine
proof that every branch has a successful executable path.

## Non-emptiness and ruling (v)

`Nonempty P` at opsNative is **not proved**. `NativeObstruction62.no_capture`
and `.not_uniform_capture` symbolically show why it cannot hold uniformly in
arbitrary residual dictionaries: replacing the still-OPEN op132 by `.div`
precludes Produced while preserving the installed closed callbacks, including
op259. `Open13262` follows the initial source steps to this obstruction; it
does not evaluate a concrete prover. This is an adversarial residual dictionary,
not a counterexample to the shipped native implementation.

**Ruling (v) MODEL WITNESS: NOT ESTABLISHED.** No explicit nondegenerate
existential dictionary satisfying all nine links simultaneously was completed.
The rejecting dictionary is not that witness. Skeleton consistency therefore
remains UNVERIFIED; no vacuous implication is credited as a run witness.

## Checked progress and remaining links

Focused accepted declarations include:

- Native binding, residual composition and field frames; original ActualRun,
  QueryContext, QueryRange and layout specialization at opsNative.
- Generic block-indexed circle unit certificates and native circle source/origin
  transport; backend material length 29.
- Symbolic slice, row and loop bounds for compact semantic encoding, with failure
  and partial-error paths retained. No concrete prover evaluation was used.
- `NativeFrontRoom62.complete`: the original front-room inequality at opsNative,
  header length 16, semantic bound 55*13831, claim bound Usize.max/2. This is
  unconditional even over the total publication fallback paths.
- `NativeFrontRoom62.publishOrder`: the unchanged original PublishOrder link.
- `NativeBackendFacts62.trace` and `.coefficients`: caller C1/C2 material trace
  and canonical coefficient facts at opsNative, not the full hinput producer.

| Required full link | Result |
| --- | --- |
| QueryAppend | OPEN; source append association not discharged |
| FinishContext | OPEN; complete finish context not discharged |
| NodeAppend | OPEN; six-slot tail draft failed default recursion depth; sorted/dedup publication association also remains |
| CommonSample | OPEN; model unit laws pass, full native circle-coordinate transport hit default heartbeats; complete stored-record association remains |
| BackendInput | OPEN; trace/coefficient facts pass, full hinput cell association remains |

The failed `CircleNativeLaws62` and `NativeNodeTail62` sources are retained but
are not accepted proof modules. `CircleChallenge62`, `NativeSample62` and
`CircleGoal62` are uncompiled drafts and earn no credit. No limits were raised.
The last node attempt (70695) reached a capacity expression whose normalization
hit maxRecDepth; next work needs named symbolic six-slot capacity projections.
The circle bridge needs a smaller carrier/coordinate transport lemma, not a
larger heartbeat limit. Rejected SHA/revision records are preserved in
retained-failed-sources.json; rejected source was not resubmitted unchanged.

No unconditional `RUNJOIN_PUBLISH_COMPACT` instance was composed. Exactly three
TrustItems remain. **Rows removed: none. Endpoint premise reduction: zero.**
All existing privacy, source-fidelity and side-channel limitations remain.

## Verification and resource evidence

100 attempts: **78 accepted, 22 rejected**, including 57 prerequisite compiles
and the three accepted audits. Cumulative host wall time 952.81 seconds; maximum
RSS 4,501,233,664 bytes (4.19 GiB); swap 0. No memory kill. Every launch used its
own admitted systemd scope, MemoryHigh=6 GiB, MemoryMax=8 GiB,
MemorySwapMax=0, TasksMax=64 and Lean -M7000. Three unlaunched admission refusals
were retried only after the required cooldown with the same unused ID; they
were not compile attempts. No package-wide replay or unrelated regression ran.

Final fresh preflight before audit staging: 3925 project source/object pairs,
8729 direct dependency fingerprints, 5673 external objects and 5438 IR companions,
all matching in the pinned host workspace. Native-h6 reuse verified 63 matches;
15 mismatched candidates were rejected and not loaded. Historical prerequisites
were compiled one module per scope against this cohort; no cold dependency
build was launched. Audit imports were staged from committed exact sources.

`verification.tsv` records every exact target, exit, wall, RSS, swap, source
revision/SHA and printed axioms. Each receipt and original module record is
retained; original output is SHA-verified in original-module-logs.json.xz.
The three reserved audits printed **all 60 expected accepted run62 declarations**,
with no missing or unexpected declarations and no nonstandard axioms:
only propext, Classical.choice and Quot.sound (or no axioms).
See axioms-audit.json, SUMMARY.json, fresh-preflight.json and boundaries.json.
Failed proof diagnostics do not receive this audit credit. No full frozen
manifest/release claim is made while witness and links remain open.

## Next exact work

1. Supply source-qualified success packages for V228/V244/V263 and allocator
   obligations, or separately build the labelled ruling (v) existential model
   witness with actual constants and all nine links; no native credit for it.
2. Complete QueryAppend and FinishContext, then named six-slot NodeAppend
   capacities plus sorted/dedup publication-index association.
3. Finish CircleSelected coordinate transport and full CommonSample, then
   C1/C2 material-to-hinput cell association for BackendInput.
4. Only after non-emptiness and all links, compose the unconditional endpoint
   and perform its focused axioms audit. This run has no remaining compiler IDs.
