# TX2 native handoff

Branch `codex/cx-tx2-native-20261026`. All stages committed locally; no push.
S2 remains OPEN; the 100-bit target is not yet established.

Final top: `AspisR1.T2Nat_NativePair.accepted_pair_unified`,
`lean/T2Nat_NativePair.lean`, checked T2Nat_068 and audited T2Nat_069.
Stop reason: BOTH assigned rows removed in this joint endpoint. No budget
exhaustion or checked counterexample against shipped source is claimed.

## Before and after

Before: `CPhy_Physical.accepted_pair_unified` exposes one actual installed
reader return and one actual finish on the returned/flushed accumulator, with
FinT's conditional Boolean model agreement. Native raw/scalar/semantic/validator/
iterator composition and complete finish Result/log transport remain local gaps.

After: the SAME `f,s,cuts`, retained checkpoint bytes, Prepared/Accumulator,
query return, flush writeback and finish view now export:

- The concrete emitted native reader Result on the very same op18 arguments;
  actual length1768 and allocation admission `reserved=true`, derived from that
  installed call, with no separate reader, allocator-success or state premise.
- For EVERY incoming ordered log, one derived outgoing log shared by native
  and retained reader programs with that SAME full returned pair. Helper
  substitutions preserve returned Checkpoint errors and decoder error priority;
  the three oracle calls and their operands remain in the unchanged prefix.
- The entire finish Result through the actual caller error adapter and its
  ordered log contribution on the actual returned accumulator. Source-order
  Relation/Query error normal form is proved under the existing total primitive
  leaves; full source/adapter erasure includes outer fail/div too. The finish
  adds no digest events and retains any preceding ordered history exactly.

All old CPhy conclusions and conditional Tx2N Outcome remain. There are NO new
hypotheses, narrowed input carriers, changed quantifiers on old conclusions,
independently successful executions or cryptographic/security-metric changes.
Exact source statements: T2Nat_before-statement.lean.txt (CPhy input) and
T2Nat_after-statement.lean.txt (final top). Definitions EqOk, EqRun, ReaderOps,
native reader, OnRun and installed finish are expanded in audit069/stdout.log.

## Ledger delta

| Removed row | Checked discharge in this endpoint |
|---|---|
| L175 / finish full effects | FinishCode/RoundCode erasure, FinishResult installed_erase/full_result/installed_effects; T2Nat_Accepted and final NativePair on the original returned accumulator |
| L172 / reader native/helper composition | RawBounds/RawJoin, ScalarJoin, SemanticJoin, WeightSequence and ReaderOps; exact source fissions, ReaderJoin.on_run and ReaderEffects.on_run at the actual op18 return; final NativePair |

Added row IDs / added trust items: NONE. The global premise-ledger file was
not edited, respecting the prefix-only instruction; this is the lead's delta
against that ledger and the CPhy handoff, not a claim about other workers' rows.

## Non-vacuity, conditioning and retained boundaries

FinishNonvacuity.success_log constructs a successful full Result/log from the
retained local primitive interpretation; round_fission checks expansion of
the round leaf without losing effects. ReaderNonvacuity.empty_rejects constructs
an actual native Checkpoint-error return with no digest-success premise;
raw_total constructs exact native raw successes for EVERY in-bounds cursor
and arbitrary byte contents. Every new joint fact is derived from the original
accepted pair, so none imposes an additional acceptance restriction. This is
not a proof that all remaining SDK/cryptographic premises have a joint deployed
accepted inhabitant.

EqOk/EqRun preserve every OUTER ok return, including inner Err values and their
ordered logs; they do not distinguish outer fail from divergence. The joint
endpoint is conditioned on the original accepted entry calls. This is not full
R22 totality, a global rejected-outer-failure oracle experiment, or an ELF theorem.
The finish's separate full-Result erasure does retain outer fail/div.

Retained unchanged: SDK borrow and TrustedStd contracts, allocator/runtime/ABI
admission, inherited extraction/P6/source-to-artifact association, P1/syscall,
site projection/global effects, protected cross-TX checkpoint version, P2Prime,
FirstEntry provenance, immutable Session A prepare/arithmetic/domain owners,
WhenBound and authenticated_S1 gates, query budgets and all other cones.
No missing implementation proof is relabelled as a crypto assumption.
Next lead deliverable: consume NativePair in the remaining global source/oracle
experiment and authentication/WhenBound integration, within those same boundaries.

## Validation and resource receipts

69 submissions conservatively charged of100;68 Lean invocations (39 pass,
29 fail), plus043's own missing-dependency preflight rejection before Lean.
0/30 Kani. Final audit069 prints ALL88 new theorems: only subsets of
[propext, Classical.choice, Quot.sound], or no axioms. Failed-source audits
are excluded. T2Nat_validation-index.json maps EVERY current source hash to
its successful exact receipt; each receipt records target, argv, source revision
and SHA, selected dependency hashes, exit, wall, peak RSS, swaps and full axioms.
The source revision anchor for final targets is79e71ba851 plus exact dirty source
snapshots, unchanged by the final evidence-only additions.

| Final target | Attempt | Exit | Wall s | Peak RSS KiB | Swaps |
|---|---|---|---|---|---|
| ReaderJoin |061|0|1.871260196|5181244|0|
| ReaderEffects |067|0|1.981177169|5178580|0|
| NativePair |068|0|3.116320145|5265980|0|
| Audit |069|0|1.828928717|5194172|0|

Every compile used the existing S2W launcher, Lean4v4.32.0, lake env lean-j1
-M7000 -DElab.async=false, and a verified distinct systemd scope with
MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64. Never raised caps. Kernel
memory failures018/051/053 and recursion/heartbeat failures031/039 were replaced
by symbolic sequencing or smaller named source cuts, never unchanged reruns.
The final replacements are020/021,037/044/046/048/049 and052/054/055/056.
All failures remain committed diagnostics. Final host snapshot: only init.scope.

The coherent SInt2 workspace and its existing objects were reused. Final object
and reused baseline hashes/sizes are in T2Nat_final-object-manifest.json; no
objects/binaries are committed. This is focused coherent-cache compilation,
not a fresh frozen-release replay. No package/full-manifest or unrelated suite
ran. Source whitespace/prohibited-proof checks pass. Raw tool logs are preserved
verbatim, including their whitespace.

T2Nat_admission.json rechecks both historical scalar Kani successes, all173
source pins per certificate, snapshots and pre-harness helper definitions.
All match. Timed-out whole reader005/008 remain excluded; no Kani replay.

## Frozen artifacts and scope

No shipped/cfg(kani) source, parameter, feature, wire format, key or other
worker prefix/worktree was changed. No Rust/Kani/SBF rebuild trigger fired.
Inherited ELF pins, NOT freshly reproduced:

- default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
- devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
- Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548

No Session A live worktree or S1/S3/S4/S5/S6/S9 candidate was modified. No
wallet/account keys or funds were touched. All commits are local; no push.
