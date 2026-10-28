# FXIO result

**Target not yet established. No rows closed; no endpoint premise removed.**
Branch `codex/pv-fxio-20261028`, based on
`10b8afe7647d478f70693d8fc12e07be871c91e0`, in exactly the assigned worktree.
No changes under crates/ or programs/, no merge/push, no key/account operation.

## Checked finding FXIO-1

The original emitted op22 is a pure callback with options and path inputs,
returning the complete nested Result and no filesystem world. Identical native
create_new calls at the selected shipped boundary produce success then
AlreadyExists. The emitted store returns its unchanged directory and clears
last_error on success; repeating with that store and nonce cannot advance
external filesystem state through a fixed pure dictionary.

The finding refutes the proposed **fixed-dictionary original-carrier universal
source association**, not Rust create_new, the conditional privacy theorem,
or all explicitly stateful/world-indexed interpretations. It is not merely a
bad-copy mismatch: the logical obstruction quantifies over any pure callback
and fixed projection of its complete result. Source association still uses
script-checked signatures/body inspection, not a Lean import of the entire
extracted caller. FINDING.md states the exact scope and repair.

Proved: `PV_FXI_RepeatCreate.no_fixed_complete_result`, `no_fixed_callback`,
concrete distinct outcomes, non-vacuity and a working world-threaded reference
pair. Env-J35801 passed, eight axiom reports all empty; 0.22 s,
487,912 KiB RSS, zero swaps. Env-J35800 failed on a reserved field name;
changed source fixed it. Failed sorryAx elaboration reports receive no credit.

Measured: optimized pinned-nightly native suffix validation, exit 0,
0.16 s, 119,500 KiB RSS, zero swaps. The exact shipped 681-byte suffix returned
true then false/EEXIST(17); all 80 content bytes were preserved on repeat.
Evidence class: **finite validation**. This tests no crash/recovery claim.
Structural source gate: **structural (K-1 substitute)**, partial obstruction
evidence only, covering pinned stdlib open/options/open64/flags/error dispatch.
It does not close a row or prove universal syscall semantics.

## Per-row before/after

| Row | Status | Remaining obligation |
|---|---|---|
| V171 op14 | OPEN → OPEN | Complete File.open result/state/ownership law and original-carrier installation |
| V172 op15 | OPEN → OPEN | Complete fsync errors/world effects; persistence under crash not proved |
| V175 op22 | OPEN → OPEN | FXIO-1; thread shared filesystem state through the original caller |
| V176 op23 | OPEN → OPEN | Complete representation/errno decoding and world frame law |
| V267 op261 | OPEN → OPEN | Arbitrary partial writes, errors, Interrupted retry, WriteZero and state law |
| V268 type3 | OPEN → OPEN | Full Error interpretation/transport; no Formatter axiom introduced |
| V271 File | OPEN → OPEN | Live ownership, exactly-once close/Drop and shared-world transport |

Before/after endpoint statement, carriers, adversary, observer, simulator and
failure event are unchanged. Premises removed/added/weakened: **0/0/0**.

## Trust and stopping

T remains exactly entropy_law, entropy_kernel, observation. The entropy fields
supply no filesystem facts. observation equates already-defined native and
extracted outcomes, ordered calls, filesystem state and the complete observer;
it does not independently supply availability, atomic create, write progress,
post-error rollback, crash persistence or witness-independent failure laws.
OS-CONTRACT.md gives each row's coverage. O_EXCL atomicity and fsync/storage
crash persistence are possible additional owner-level facts if not proved;
they were **not assumed or installed** as T items.

Stopped at the checked fixed-dictionary source-association obstruction.
Budget: **2/100 Lean attempts, 0 Kani**, only 35800–35801 consumed; audit IDs
35897–35899 unused. No rows completed, hence no row-closing combined audit or
closure replay is represented as passing. All 5,673 external objects were
hash-verified before compilation. Full cap/target/revision/hash/axiom receipts
are retained. SSH failures were retried with cooldowns, read-only after
submission; no compilation was resubmitted unchanged.

Next concrete deliverable: an explicit filesystem-world interpreter and a
proved caller-level threading/transport theorem covering success and errors,
partial writes, sync and Drop. A per-call dictionary without that transport
would change the statement rather than discharge it. A source rewrite remains
only proposed and requires the lead's route decision.
