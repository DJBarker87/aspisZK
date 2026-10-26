# Runtime9: checkpoint association and collision-event transport

**Target not yet established. Zero premises removed from Rc8_Top.deployed.**
Branch `codex/cx-l159-runtime9-20261026`; local stage commits only; no push.

## Exact proved results

A: `SCJ_Checkpoint.same_saved/entry_saved` apply the CPH history proof on the
same supplied native cuts. `SCJ_NativeLoaded.entry_loaded` removes the supplied
cut prerequisite by deriving native cuts from both accepted wrappers.
`SCJ_NativeLoaded.ideal_cut` then transfers that physical entry-buffer equality
to ANY ideal source dictionary's cuts on the SAME e1/e2/saved indices. Thus
native/ideal dictionary inequality itself does not block checkpoint transport.
The approved CPH game converts via recordedInstance to the consumed CPG game;
no history record, byte equality or additional runtime trust is assumed.

The actual all-oracle SCI association remains uninstantiated: supplied native
acceptances/game entries must be the response-selected entries and saved Vec
of that ideal run at EACH H. No fixed-sha P1 hypothesis is universalized.
The checked local CPH result is not advertised as discharge of that factory.

B: `SCJ_Projection.event_implies_refuted` proves that the proposed implication
from sublist inclusion alone is FALSE for the exact release iv and Q+2965.
The retained witness has small=[(bytes one,two),([],one)] and
full=[([],one),(bytes one,two),([],one)], both consistent with one H, literal
sublist inclusion, and only two distinct reads. The projected [] read is
fresh after bytes one; the full [] repeat is cached. Therefore projected event
is true and full event false. This refutes the sublist justification, not a
source/account security theorem or a jointly instantiated deployed attack.
`SCJ_OrderObstruction` checks the precise lost first-occurrence order.

A valid sufficient repair IS proved: `SCJ_Projection.event_implies` in
SCJ_OrderedTransport takes read inclusion and FIRST-occurrence order preservation
on projected addresses, consistency in one H, and the full budget. It derives
the exact event direction, requiring neither equality of logs nor events.
`SCJ_AccountProjection.event_implies` specialises to the two actual F3X/SCE
recorder carriers and DERIVES the full Q0+Q1+2965 budget from SCF_Charge, with
no extra loss. Its implementation-specific read/order instance remains OPEN.
`SCJ_Alignment/AlignedEvent/EventTransport` give a second local-invariant
interface; `SCJ_FirstRead.cached_interior` proves safe interior cache-hit deletion.

## Composition attempt and remaining obligations

`SCJ_Domination.of_transport` and `SCJ_Composition.account_of_branch` compile
with the implication exposed. The latter consumes SCI's exact recovery
consumer and retains source acceptance, raw-or-projected-collision, and the
chronological source/account join. These are conditional consumers, not new
trust or a premise-removal claim. `indicator_obstruction` shows the projected
indicator can exceed the full charged indicator under arbitrary sublist
projection. `SCJ_Top.unrestricted_runtime_obstruction` excludes a bound on every
unconstrained Runtime; it does not refute a theorem on the actual SCE runtime.

No unconditional domination instance or SCJ_Top.deployed is fabricated.
Remaining concrete work: index CPH on the actual per-H selected pair; derive
source acceptance; prove actual recorder read/first-order association (or
refute that specific instance); prove the physical account's recovery interface.
SCI's `ordered` hypothesis is NOT obtained from event implication. Alternatively
use SCF_Recovery.agreement's exact semantic-public, three frame and three cut
equalities on this same account. Then compose the bound at the actual endpoint.

## Before/after and ledger method

SCJ_BEFORE_SOURCE.lean.txt and SCJ_AFTER_SOURCE.lean.txt are identical Rc8 source.
SCJ_BEFORE_KERNEL.lean.txt and SCJ_AFTER_KERNEL.lean.txt are identical fresh kernel
statements from SCJ_022, with no omitted tails. No endpoint quantifier, carrier,
failure event, conclusion or antecedent changed. SCJ_LEDGER_DELTA.json recomputes
the inherited Rc8 atomic rows, preserving scope and aliases L137/L134 and
L185/L159. Raw actual83T/19P/13G; distinct actual83T/18P/13G; distinct non-alias
deployment-inclusive89T/22P/13G. Removed0/added0/reclassified0. L159/L185 and L181
remain. The source-global and native-local finish families remain separate.
132 distinct expanded boundary/carrier declarations receive fresh isolated
kernel inventories; these checks earn no security-closure credit.

## Non-vacuity and trust

SCJ_Nonvacuity.real_bytes rechecks the SCE/JFx retained proof/public bytes and
the selected second entry's saved CP. SCG_Nonvacuity.joint is imported read-only:
actual model SDK/std/admissions, native local successes, approved game,
persistence, observer bytes and charge budget coexist. These LOCAL model native
functions do not instantiate installed cryptographic extraction. Neither this
fixture nor Rc8_Nonvacuity.composed proves joint inhabitance of every release
premise; the JFt_ joint gate is not claimed closed.

Only standard axioms occur in the accepted final theorem closure. Two exit-zero
development/diagnostic attempts are EXCLUDED: SCJ_019's local `loaded` theorem
shadowed the unqualified CPG_Projection.loaded in a section variable, creating
implicit sorryAx; SCJ_023 printed that rejected term. SCJ_024 renames it to
entry_loaded and qualifies the loaded projection; SCJ_025 prints the repaired
standard-axiom term. Three ordinary development errors (002/005/010) are also
excluded. All exact receipts/snapshots remain; exit zero alone was not accepted.

## Frozen scope and validation

Only new lean/SCJ_ modules and this receipt directory changed. No existing
proved module, shipped/cfg(kani) file, session-A worktree/candidate, key, wallet,
authority, ELF, protocol or metric changed. ELF rebuild trigger did not fire.
Historical pins are inherited, not newly reproduced:
default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4;
devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299;
Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.


## Final validation and stopping point

Budget EXHAUSTED: **100/100 Lean compile attempts, 0/0 Kani**. Exactly95
accepted attempts; five excluded development/diagnostic attempts, comprising
three compiler failures and two exit-zero axiom-rejected diagnostics. Every
CURRENT own source has an exact-source accepted pass. No dependency build,
Rust/SBF build, package replay or frozen-manifest replay ran.

SCJ_100: target SCJ_FinalAudit.lean, exit0,
wall2.468216865963768s, peakRSS5517644KiB, swap0,
source revision 744cca1cc9c70d8893705db54d3723fb0a307ac2 (dirty tree; exact hash in receipt).
It audits ALL24 new theorems, the ACTUAL Rc8_Top.deployed,
Rc8_Nonvacuity.composed and SCG_Nonvacuity.joint. All final axiom sets are
subsets of propext/Classical.choice/Quot.sound, or empty. It also checks the
full types of the top, ideal checkpoint bridge, sufficient projection theorem,
actual recorder specialisation and conditional composition consumer.

Aggregate compiler wall233.39806909370236s; maximum peakRSS
5529404KiB; swaps0. Every attempt uses Lean-j1-M7000-async=false
inside MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64, one scope at a time.
No timeout, memory kill, cap raise or unchanged failed-source retry occurred.
SCJ_023 followed the required vanished-other-cgroup30s retry; the initial
observed diagnostic and inherited orchestrator's log-overwrite behaviour are
recorded in SCJ_ADMISSION_NOTES.md. No barrier was bypassed.

SCJ_HOST_MANIFEST.json pins all94 own final sources/objects, selected
root dependencies, unchanged launchers and inherited SInt2 cache manifests.
All own and named root host sources match local SHA-256. The final audit's
selected direct objects match those final pins. This is focused validation on
the coherent retained workspace, NOT a fresh release-wide coherent replay.
Source-only scope and the zero-delta ledger are checked offline by
SCJ_validate.py --final; exact receipts, snapshots, hashes, dependency
fingerprints and axiom lines are retained. SCJ_attempts.jsonl is the complete
100-attempt ledger. No binary/object/ELF/archive is committed.

All stage commits remain local. No push or merge. The100-bit target remains
not established. The next deliverable is the actual per-world CPH association
and actual recorder first-order/recovery instance, then unconditional
account domination and a deployed endpoint that really removes L159/L185/L181.

Final offline validator passes, and staged `git diff --check` passes. All work
is confined to new SCJ_ Lean modules and evidence/l159-runtime9-20261026/.
The working tree is committed after this handoff; obtain the local stage
history with `git log --oneline $(git rev-parse 956b8d1a74^)..HEAD`.
