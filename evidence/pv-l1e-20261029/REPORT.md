# L1E top-down count composition — D466

Branch `codex/pv-l1e-20261029`, base `147b8a7ec3`, exact sparse worktree
`/Users/dominic/ZK/.worktrees/pv-l1c`. No push or merge. COUNT remains the
first input; ORACLE, TIME and RETAINED_SIDECHANNELS have not been started.
**Target not yet established. No native producer input is installed.**

## Skeleton and what it actually tests

`PV_L1E_OriginalCountSkeleton.original_count_trace` concludes EXACTLY
`PV_RJ4IDB.OpenInputs.L1_COUNT_TRACE actualCount native`.
It compiled at ID 66507, the seventh actual Lean compiler start. The generic
transport compiled at 66502. The initial 66500 proof-text error is retained;
the proof was changed before retry. Failed sorryAx output earns no credit.

The original skeleton parameters are independent `actualCount`, `native`,
`sourceWorld`, `bodyWorld`, original `owner`, `initial`, `fuel`, `index` and
`adapt`. It uses the SAME expression
`adapt i (run (owner i) (fuel i) (index i) (initial i))` at both joins. No native
family is defined as its decoder projections, and no new simulator, failure
event, witness restriction, or trust item is introduced. The adapter is an
explicit, unconstructed source-world operation, not a certified native decoder.

Its four standalone named Prop links, with exact statements, are:

1. `PV_L1E_CountSkeleton.PV_L1E_Link_CountAcquisition actualCount sourceWorld`:
   `∀ i, actualCount i = (counts (sourceWorld i).events,
   rejections (sourceWorld i).events)`.
2. `PV_L1E_CountSkeleton.PV_L1E_Link_BodyWrapper sourceWorld bodyWorld`:
   `∀ i, sourceWorld i = bodyWorld i` (full ordered Trace and terminal).
3. `PV_L1E_OriginalCountSkeleton.PV_L1E_Link_OriginalRetry bodyWorld owner
   initial fuel index adapt`:
   `∀ i, bodyWorld i = adapt i (run (owner i) (fuel i) (index i) (initial i))`.
4. `PV_L1E_OriginalCountSkeleton.PV_L1E_Link_NativeD163 native owner initial
   fuel index adapt`:
   `∀ i, adapt i (run (owner i) (fuel i) (index i) (initial i)) =
   modelTrace (native i)`.

The source file and original compiler output give all binder types. Each link
is stronger than a mere complete-Result law and none repeats the target
`actualCount = native count/rejection projections`. Definitions are frozen:
no weakening or replacement is used to claim discharge.

**Limitation exposed early:** this proves the algebraic interfaces fit when
supplied. It does not instantiate the original honest experiment, native world,
client adapter, or simE coupling. In particular the typed COUNT input itself
contains no distributional or simE assertion. A proof of that necessary
pathwise decoder law would still require the joint original-to-simE law for
V348/V351. No generic equality transport is counted as premise removal.

## Link status and source work

CountAcquisition: OPEN. Actual acquisition of published count, rejection
indices and operation histories from the client/source world is absent.

BodyWrapper: OPEN as stated (full ordered trace). The complete-Result wrapper
and its dependent recursive retry source proof are separate focused targets;
no Result erasure is promoted to event equality.

OriginalRetry: OPEN for the deployed source and all admitted prefixes. D163's
total owner describes complete terminating ordinary-error runs. Its conservative
embedding in Logged is being checked separately. Outer extraction fail/div,
panic/abort and interrupted prefixes need the explicit runtime/world extension.
No normal-stop replacement for those terminal forms is authorized.

NativeD163: OPEN. Native leaf/callback/world/Drop/unwind association (V163,
V167), client publication/account/upload association and the SAME original
failure coupling remain unproved. The original-to-simE joint law is retained;
it is not a fourth trust item.

All three full deployed retry/callback source files and complete body spans
still match pv-diag2's own-1 control binding: `retry-source-reuse.json`.
Evidence class remains structural source-controller binding (K-1 substitute
scope), with inherited leaf/effect/Drop/unwind obligations and V370 at pending
D381/D386. This is not a new execution, native event law, or b3p6-1 claim.

## Other inputs and unchanged security boundary

L1_COUNT_TRACE: PARTIAL, conditional exact skeleton only; concrete native
instance OPEN. L1_ORACLE_PREFIX, L1_TIME_TRACE, and L1_RETAINED_SIDECHANNELS:
OPEN, not started under the requested input ordering.

D359 enters exactly where a full joint elapsed-duration law invokes the
owner's pending decision on measured timing evidence from a throttled host.
No outcome of that decision is assumed. Allocation, addresses, durability,
environment, clocks and cross-channel order remain retained.

Before/after headline/deployment premises removed/added/weakened: **0/0/0**.
V347–V351 remain OPEN/P. T remains exactly entropy_law, entropy_kernel,
observation. No checked honest-native secret-dependent leak finding is claimed.

## Validation

Final compiler totals, audit receipts and source/cache validation will be
inserted after the focused targets and one final focused replay.
