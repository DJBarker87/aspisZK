# D540 resume: composed prover source spine; complete event task unfinished

Branch `codex/pv-evh-20261029`, exact worktree
`/Users/dominic/ZK/.worktrees/pv-evh`. This resume began at `ddd4d92391`;
EVH5 originally began at `841ae0f9a9`. **Rows removed: NONE. Target not yet
established.** This stop is an explicitly requested context handoff, not budget
exhaustion, a source counterexample, or an owner blocker.

## Established in this resume

`PV_EVH_Prefix` composes finite state/writer executions. Exhaustion, source
failure and source divergence are separate cases; state and ordered event
prefixes survive each. `FinishedView` asserts Result erasure only for finished
finite runs. `PV_EVH_PrefixLoop.fixed_recursive` transports nested finite
executions through an actual source recursive equation without normalizing a
prover recurrence. It is axiom-free. The old accepted modules were not edited.

`PV_EVH_EntropyGenerate.generate_fixed` binds the emitted nonzero guard to the
existing entropy interpreter. `PV_EVH_AccountCallback.callMut_fixed` and
`next_fixed` follow the actual proof-account FnMut callback and wrapper,
retaining the exact `(r1,t,back)` tuple and applying `back c1`. Account acquisition
is still a named D520 input. The inherited entropy `afterDraw` tail remains
Result-only for some helpers and earns no complete event-coverage credit.

`PV_EVH_PrefixRetryBody` and `PrefixRetryRun` use that nested execution carrier
through the actual retry source spine. `PV_EVH_AccountEntry.entry_fixed`
connects it to emitted `RealR1_client.prove_for_proof_accounts`, with its retry
entry guard. `PV_EVH_MaskedAttempt.run_fixed`, `MaskedWithAttempt.run_fixed`
and `ReserveBuild.run_fixed` expand the exact emitted masked-attempt,
with-attempt and reserve-and-build control spines. They use named, typed OPEN
callee interpretations, not a whole-program trace answer. Their hypotheses are
local erasure conditions, not native observation laws or new trust items.

`PV_EVH_ReserveJoin.install_fixed` replaces the whole reserve-and-build callee
with its source interpreter. `PV_EVH_ProverSpine.entry_fixed` composes the
library entry, actual account callback, retry, masked-attempt, with-attempt
and reserve-and-build spines. It has NO whole `next_OPEN`, `prove_OPEN`,
`prove_masked_with_attempt` or reserve-and-build erasure hypothesis. Instead it
retains five head callees, eighteen with-attempt callees and eleven generic
reserve callees, plus the account and entropy boundary conditions. These are
explicit unfinished leaves, not discharged source effects.

`PV_EVH_DurableReserveBuild.run_fixed` specializes reserve-and-build to the
actual durable nonce-store instance and uses existing `NonceSource.reserve`
through `Prefix.ofM`. It retains the nonce source's file request/delivery
prefixes, with ten other reserve callees OPEN. This specialization is compiled
but NOT YET installed into the generic ProverSpine composition. The old nonce
helper coverage gaps remain; this is not a full filesystem adequacy claim.

Generators check byte-identical output and retain original extraction/body
hashes, exact field signatures and open-callee inventories. No extraction,
source dictionary, NativeTrace projection or privacy theorem was edited.

## Remaining obligations and before/after

Before this resume, retry transport needed whole next/prove callee laws. The
new LOCAL composed source-spine theorem expands those calls into their exact
control graphs and named leaf laws. Before/after at the PRIVACY endpoint:
all nineteen runtime selections and all native/deployment/privacy premises
remain OPEN and unchanged. No ledger row is removed. No simulator, observer,
T field, error term, actual-family quantifier or NativeTrace definition changes.

The complete source event producer is still missing. In addition to the named
leaf inventories, Result-only entropy/nonce helper tails and the retry-entry
comparison (op233 under its trait default) still lack event interpretation.
Source failure Results alone do not emit native panic/abort diagnostics.
Allocation/drop/runtime paths, hash request/answer byte fidelity, complete
oracle/count/file trace projection links and rtDeployed installation remain
unproved. Count projections must allow events from ALL instantiated callees.
D520 client-before/after and account acquisition stay explicit for pv-uc/U/D524.

No successful full run at runjoin opsNative and allocator world, complete
actual-family link conjunction, or actual-domain nonemptiness is proved.
NativeObstruction62/op132 still prevents inferring uniform success. Ruling
(v') consistency reduction has NOT been earned by these conditional local
lemmas. The measured headline at `8fa34d9fb4` is unchanged; no finite-carrier
work or alternative event definition was introduced. V370/V371/rdea-1,
V400/V396, D159/D166 and L1/L2/L3 retain their existing classification.

## Validation, resources and budget

Initial read-only audit reconciled all 19 inherited EVH5 receipts and accepted
objects with the host and found no live owned scope. Every new compile used
the retained workspace/cache and verified SAME project/external cohort and
first-root namespace resolution before launch. No dependency was rebuilt.
There were no admission refusals, transport errors or memory/time kills in
this resume. All scopes used same-shell admission exit 0 and allowed:true,
MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64, Lean -M7000.

| Accepted target | ID | Exit | Wall | RSS KiB | Swap |
| --- | --- | --- | --- | --- | --- |
| PV_EVH_Prefix | 73642 | 0 | 0:01.69 | 2588912 | 0 |
| PV_EVH_EntropyGenerate | 73644 | 0 | 0:01.42 | 2582928 | 0 |
| PV_EVH_AccountCallback | 73645 | 0 | 0:01.64 | 2585012 | 0 |
| PV_EVH_PrefixRetryBody | 73647 | 0 | 0:01.93 | 2595220 | 0 |
| PV_EVH_PrefixLoop | 73648 | 0 | 0:01.54 | 2580316 | 0 |
| PV_EVH_PrefixRetryRun | 73649 | 0 | 0:01.50 | 2581352 | 0 |
| PV_EVH_AccountEntry | 73650 | 0 | 0:01.61 | 2586556 | 0 |
| PV_EVH_MaskedAttempt | 73651 | 0 | 0:01.88 | 2600204 | 0 |
| PV_EVH_ReserveBuild | 73654 | 0 | 0:02.91 | 2605996 | 0 |
| PV_EVH_MaskedWithAttempt | 73656 | 0 | 0:09.32 | 2645220 | 0 |
| PV_EVH_ReserveJoin | 73657 | 0 | 0:02.78 | 2591336 | 0 |
| PV_EVH_ProverSpine | 73658 | 0 | 0:03.17 | 2595284 | 0 |
| PV_EVH_DurableReserveBuild | 73659 | 0 | 0:02.60 | 2616092 | 0 |

Each `receipt-ID.json` records exact target, source revision/blob/SHA,
dependency fingerprint, command, admission, exit, wall time, RSS, swap and
#print axioms. Accepted theorem axioms are subsets of propext,
Classical.choice and Quot.sound. All five failed elaborations retain their
original source/receipts and have no credit: namespace alias, loop equation
arity, parenthesized result carrier and generated local-alias tactics. The
last category required two source fixes. No arithmetic recurrence was reduced.

The failed-source guard caught a byte-identical regeneration BEFORE ID scan
or submission at 73655. `guard-73655.json` records that uncharged refusal. The
actual later 73655 launch used changed generated bytes. The guard itself was
unchanged; no failed source was recompiled unchanged. No ID was reused.

`audit.py` now checks every focused receipt dynamically plus all generator
outputs. `validation.json` and `host-final.json` validate all 37 EVH5 receipt
sets, accepted source/objects and absence of live owned scopes. The scan of
this resume's paths and forbidden proof constructs passed. No file exceeds
20 MB. There was no separate final closure/audit launch: full event acceptance
is unfinished, and audit ID 73699 is preserved. No unchanged release regression
was repeated. No Kani/native run, key/account/funds operation or push occurred.

Usage this resume: **18 attempts, 13 accepted, 5 failed** (73642–73659).
EVH5 total: 37 attempts, 17 accepted, 20 failed. Cumulative with EVH4:
**54/100 attempts spent, 46 remaining**, 0 native and 0 Kani. Next fresh ID
**73660**; audit **73699** unused. The existing 73697/73698 stay consumed.
The committed HANDOFF.md gives the exact next implementation steps.
