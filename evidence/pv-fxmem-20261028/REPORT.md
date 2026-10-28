# Memory callback finding

**Target not yet established. No row closed and no deployed endpoint premise
removed.** Branch `codex/pv-fxmem-20261028`, base `10b8afe764`, worktree unchanged.

Stopped at the checked V170 obstruction detailed in [FINDING.md](FINDING.md).
A fixed original `op4 : {T : Type} → T → Result Unit` cannot reproduce normal
return and panic for the same input in two different accessible worlds. The
native witness uses an inhabited zero-sized type with a destructor that reads
an external flag. This refutes the explicitly stated **fixed, world-independent,
generic complete-Result projection**, not Rust drop or every possible world-indexed
formulation of the row. It does not allege this destructor occurs in a shipped
caller. No Drop-free restriction has been substituted for the generic statement.

The next deliverable is an explicit effect-aware/world-indexed callback
interpretation and its consumed execution composition, or proofs about exactly
the consumed types/destructors that justify a narrower installation. Neither is
silently assumed here. The logical proof explicitly constructs a state-indexed
interpreter as a non-vacuous repair example; it is not a native refinement.

| Row | Result |
|---|---|
| V170 / op4 drop | OPEN; checked counterexample to the fixed generic projection |
| V183 / op32 try_reserve_exact | OPEN; no allocator/error/capacity installation supplied |
| V221 / op122 Array Zeroize | OPEN; no volatile-write/restoration/fence installation supplied |
| V222 / op123 blanket zeroize | OPEN; no default/volatile-write/fence installation supplied |

Proved: the five theorems in
`docs/research/v8-r0-zk-20261009/lean/R1Z/PV_FXM_DropCounterexample.lean`.
They are Init-only logical facts; they do not assert that an owned source model
is an extracted native destructor. The generic contradiction applies to every
result representation with two distinct outcomes, including a complete Result
classification which distinguishes normal return from panic/nonreturn.

Measured: **32 paired finite-validation cases** on pinned nightly-2026-06-01,
optimized with `-O`, using real `core::mem::drop` and an owned wrapper. All pass;
both flag values enter Drop exactly once. Unwind policy is explicit. No Kani,
compiler non-elision, allocator trace or deployed-path equivalence is claimed.
`PREFLIGHT.json` records the complete pinned stdlib drop source shape/hash and
all 601 Init object hashes checked against the h4 external manifest before any
Lean compile. The scanned ID range had no existing receipt/submission hits.

| Run | Target | Exit | Wall | Peak RSS KiB | Swap | Source revision | Axioms |
|---|---|---:|---:|---:|---:|---|---|
| native01 | driver, rustc absent from PATH | 127 | 0.00s | 1760 | 0 | 7b5b43fcd7 | N/A; compiler never started |
| native02 | optimized compile + 32 finite pairs | 0 | 0.11s | 112640 | 0 | 7b5b43fcd7 + recorded changed driver hash | N/A native |
| 35500 | PV_FXM_DropCounterexample | 1 | 0.18s | 474920 | 0 | cf19921d80 | rejected; one elaboration error/sorryAx, no credit |
| 35501 | changed PV_FXM_DropCounterexample | 0 | 0.19s | 482492 | 0 | e82e62c591 | all five queries: no axioms |

Exact targets, full source revisions/hashes/blob IDs, raw logs, admissions,
dependency fingerprint and axioms are in the numbered/native receipts. All
scopes used MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0. Native scopes used
TasksMax=64; the standing shared Lean launcher used its accepted TasksMax=128
and Lean -M7000. There was at most one capped scope per job. SSH failures were
recovered read-only or retried before submission; no unchanged submitted
compiler was rerun because of missing receipts. Attempt 35501's precompiler
transport failure consumed no ID. The source changed between 35500 and 35501.

Budget: **2/100 Lean, 0/0 Kani**, 98 Lean attempts unspent at the checked-finding
stop. Audit IDs 35597–35599 unused. No complete-row combined audit or closure
replay was run, because no complete row was obtained. The finding itself has a
focused compile and five successful axioms queries.

Before/after: all four recount-6 P obligations remain OPEN, without changed
quantifiers, guards, failure events or conclusions. No fourth T field, source
law assumption, observer weakening, simulator weakening, carrier change or
endpoint edit was added. Zeroize volatile-write/compiler-fence laws and the L3
binary obligation remain separate and unproved by this job. All deployment,
E1/E2, real RunJoin and side-channel obligations are retained.

No crates/ or programs/ changes, ELF rebuild, fresh pin verification, local Lean
compile, push or merge. No keys were created or cleaned. This finding needs lead
review before any change to row scope or carrier interpretation.

Cleanup: `cleanup.json` records SHA-256/size and removal of only this job's native
test executable. Sources and receipts remain. No private Lean cache was created;
the new module used the standing shared launcher. No shared cache was deleted.
