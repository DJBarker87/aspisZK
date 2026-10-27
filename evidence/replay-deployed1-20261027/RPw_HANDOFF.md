# RPw specialised replay handoff

STOP at statement preflight, under the job's explicit rule: “If the original
statement itself cannot be stated over the pinned carrier without change,
stop and report the minimal statement change; do not adopt it.”

The original `FIr_FinishComparison.terminal_comparison_of_finish_success`
statement cannot elaborate in this cohort. Its `obs` binder is
`Option (verifier.Phase → Result Unit)`, but the retained `FinishModel.finish`
expects `Option (RPz7_PhaseIso.Phase → Result Unit)`. This is an error in the
hypothesis type, before the proof. The exact prior compiler diagnostic is
RPv_0508/stdout.log:1–8; the second error at line 61 is its proof consumer.
The complete original helper statement and the smallest explicit-transport
edit are retained alongside this report. No new compile was needed to repeat
that already isolated, unchanged failure.

The minimal proposed statement edit keeps every binder and the conclusion,
but changes the hypothesis term from:

```lean
FinishModel.finish R B D pub pre before challenges obs = ok (.Ok out)
```

to:

```lean
FinishModel.finish R B D pub pre before challenges
  (RPz7_PhaseIso.observerToFirst obs) = ok (.Ok out)
```

This edit is **proposed only, not compiled or adopted**. The proof call to
`S1SemanticFinishBounds.finish_success` would need the same mapped observer.
An alternative changes the quantified observer carrier to
`RPz7_PhaseIso.Phase`; that also changes the statement. Defining a new
consumer wrapper hides, but does not eliminate, the changed hypothesis term.

The existing isomorphism is not definitional identity of these two carriers.
`RPz7_PhaseIso.Phase` abbreviates `FirstCaller.Phase`. Existing laws available
for a future explicitly revised transport are
`first_roundtrip_RPz7`, `verifier_roundtrip_RPz7`,
`observer_first_roundtrip_RPz7`, `observer_verifier_roundtrip_RPz7`, and
`consumer_first_roundtrip_RPz7`/`consumer_verifier_roundtrip_RPz7`.
`finish_transport_RPz7` proves round-trip observer invariance on the retained
carrier; it does not make a raw verifier observer a well-typed argument to
retained finish. No new isomorphism or carrier equality is assumed here.

## Gates and booking

No RPw theorem or descendant port was created. No fresh
`AspisR1.RPw_Deployed.deployed` exists. Consequently complete kernel byte
comparison, root `#print axioms`, formatter reachability, and fresh declaration
audits are NOT RUN, not passed. Whether a subsequently authorised mapped
helper can yield an unchanged specialised root is UNKNOWN. This report does
not infer a root-statement difference from the local helper mismatch.

The historical complete `FJv_after_deployed.kernel.lean.txt` remains pinned by
SHA-256 and size in RPw_statement-obstruction.json. No claim is made that it
was freshly checked or byte-matched. The statement described by
HEADLINE-SPECIALISATION-DECISION-20261027.md remains unverified by this job.
L187 is NOT bookable for the specialised candidate. RPv's existing L187 booking
for `AspisR1.FJv_Top.deployed` is unchanged. No premise was removed, added,
changed, or adopted. The deployed 100-bit target is not yet established.

## Validation and resource record

Branch: `codex/cx-replay-deployed1-20261027`. Worktree:
`/Users/dominic/ZK/.worktrees/cx-replay-deployed1`.
Preflight source revision: `d065449420e22d9e5dd528a080974169340d1529`.
The job-specific final budget governs: 0/150 Lean attempts, 0/0 Kani runs.
No host admission, upload, scope, compiler, Rust job, package replay, or cache
cleanup was launched. Every predecessor object was left in place. No other
worker prefix, session A worktree, existing module, shipped file, wallet/key,
or ELF changed. The cfg(kani) rebuild condition did not fire; default
f8c0ec72…, devnet 63ad3e9c…, Pool 121f3e29… are inherited pins, not reproduced.

Reused exact target: `RPv_FIr_FinishComparison`, attempt RPv_0508, source
revision `876d354ff18c680e86e84556cb1b42958ae3694c`; exit 1;
wall 2.6228139320155606 s; peak RSS 3864372 KiB; swaps 0;
MemoryHigh 6G / MemoryMax 8G / MemorySwapMax 0 / TasksMax 64.
The failed terminal's `#print axioms` includes `sorryAx` as an elaboration
error artifact. It is excluded, never accepted as a theorem or standard-only
result. The complete prior receipt, command, source SHA, selected dependency
object hashes, errors and axioms lines are embedded in
RPw_statement-obstruction.json, with hashes of the supporting source/evidence.
For this compile-free stage, new target/exit/wall/RSS/swap/axioms are N/A.

Next deliverable: lead disposition of the explicit helper hypothesis edit
above under the stop rule. If permitted, prove that transported helper in a
new RPw module, port the 36 blocked descendants, and run the complete fresh
root statement/axiom/reachability/declaration gates before booking specialised
L187. This report adopts no changed statement and requests no owner security
contract amendment.
