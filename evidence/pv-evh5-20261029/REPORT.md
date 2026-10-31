# Incomplete prover world: retry-owner Result transport

Branch `codex/pv-evh-20261029`, exact worktree
`/Users/dominic/ZK/.worktrees/pv-evh`. Resume baseline `841ae0f9a9`.
**Rows removed: NONE. Target not yet established.** This is a context handoff,
not completion, budget exhaustion, an owner blocker, or a counterexample.
The original EVH5 full-entry, trace-projection and actual-domain tasks remain.

## Resume recovery

First command was git status: clean, on the assigned branch. There was no
EVH5 directory or uncommitted evidence from the stopped session. Read-only host
inventory found no `pv-evh-*` scope or prover process to wait for/collect.
All 17 EVH4 compiler receipts' admission/output/time bytes match the host.
Cross-job ID receipt and sent.txt scan is in host-recovery.json. No compile
was duplicated. Fresh IDs start at 73623; no old admission-only ID was reused.
Resume reconciliation and the design continuation were committed before Lean
at bc50b43bdd. Client D520 before/after fields remain OPEN for owner U/D524
and pv-uc. The cx2 branch was read only, with hashes in read-pins.json.
The inherited scratchpad r1p-common.txt no longer exists; pv-common.txt,
local-lean.txt and root AGENTS.md were read, including security discipline.

## Exactly established

`PV_EVH_RetryBody.body_fixed` interprets the actual extracted retry owner's
control spine with a state/writer monad. It retains the cap guard, callback,
proof-result handling, all eleven verifier-error branches, wrapping increment,
and recursive state. Proof attempt entry emits count; Rejected emits rejection.
`next_OPEN` and `prove_OPEN` remain uninstantiated callee interpreters. FixedView
compatibility of each is an explicit local hypothesis. Their internal effects
are not implemented or hidden in T, and no whole-prover event credit is claimed.

`PV_EVH_RetrySource.source_unfold` proves that the reified iteration followed
by its done/continue resumption equals the actual extracted
`ProverRwFull.prover.retry_attempt`, using its recursive equation.
`PV_EVH_WorldRecursion.fixed_finished_recursive` transports a completed finite
writer loop to such a recursive source equation by induction, not normalization.
`PV_EVH_RetryRun.run_fixed` composes those facts: on the named fixed-view domain,
a finished finite run's complete Result equals actual prover.retry_attempt.
Exhaustion keeps state and events and has no source-Result assertion.

This is a retry SUBPROGRAM result. There is no complete worldRun for
RealR1_client.prove_for_proof_accounts or masked-attempt, no complete source
oracle/file/count projection installation, and no successful full world at
opsNative and the allocator world. No skeleton consistency reduction under
(v') is claimed until all actual-family links are discharged. No unrelated
model witness was substituted for actual nonemptiness.

Before/after: all nineteen runtime selections and privacy/deployment premises
remain open as before. Local fixed-view hypotheses were added only to the
new erasure lemmas, not to the endpoint or T. Entropy laws and observation
retain their existing classification. V370/V371/rdea-1/V400/V396/D159/D166
and L1/L2/L3 remain. No simulator, observer, NativeTrace field definition,
extraction, frozen Rust, soundness source, release ELF or pin was changed.

## Validation and attempts

Nineteen new attempts, IDs 73623–73641: 4 accepted, 15 failed. All failures
are retained with source revisions and hashes. There was no memory/time kill,
no unchanged failed-source retry, and no admission refusal. Failures were
elaboration/proof issues: exact Except continuation inference, symbolic tuple
binders, redundant tactics, namespace ambiguity and resumption extensionality.
The useful final technique is an explicit `change` for the retry continuation
and direct `.1/.2.1/.2.2` state projections. Avoid reproducing the failed tactic
routes. Failed `sorryAx` recovery output has no credit.

| Accepted target | ID | Exit | Wall | RSS KiB | Swap |
| --- | --- | --- | --- | --- | --- |
| PV_EVH_RetryBody | 73624 | 0 | 0:01.50 | 2601720 | 0 |
| PV_EVH_RetrySource | 73636 | 0 | 0:01.54 | 2608536 | 0 |
| PV_EVH_WorldRecursion | 73638 | 0 | 0:01.38 | 2584772 | 0 |
| PV_EVH_RetryRun | 73641 | 0 | 0:01.28 | 2588272 | 0 |

Each exact target/source revision/blob/SHA/command/exit/time/RSS/swap/axioms
and dependency fingerprint is recorded in receipt-ID.json. Accepted axioms
are subsets of propext, Classical.choice, Quot.sound; the generic recursion
lemma is axiom-free. Every compiler ran -M7000 in its own same-shell-admitted
6G high / 8G max / swap 0 / 64 task scope. The pinned cohort, full external
manifest and first-root namespace resolution were checked before staging;
accepted predecessors were reused. No dependency was rebuilt.

A staging SSH reset before compile was retained; after a full 60-second wait,
staging was retried and 73625 launched only once. No host infrastructure was
changed. The wrapper guard SHA is in validation.json. Generator --check is
byte-identical. audit.py verifies all new source/receipt hashes, staging
fingerprints (including committed historical snapshots), caps, axioms, scripts,
file sizes, current accepted objects and all host receipt bytes. It passed.
There was no package/frozen release replay or separate final audit, since the
full requested closure is unfinished. Audit 73699 is preserved for completion.
Host-final.json confirms no live owned scope. No key/account/funds operation
occurred, no other worktree changed, and nothing was pushed.

Cumulative usage in this 100-attempt allocation: **36 spent (13 accepted,
23 failed), 64 remaining; 0 native, 0 Kani**. Next fresh ID is **73642**.
IDs 73697/73698 were already consumed by EVH4; 73699 remains the audit reserve.
The remaining actual proof frontier and exact continuation commands are in
HANDOFF.md. commits.txt records git log from the resume baseline through the
last proof commit; the final evidence/handoff commit follows that snapshot.
