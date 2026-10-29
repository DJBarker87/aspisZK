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

BodyWrapper: OPEN as stated (full ordered trace). `PV_L1E_Source_070.complete_result` and
`PV_L1E_RetrySource.{attempt_erasure,run_erasure,complete_source,
client_no_final_rejected}` are CHECKED. They close L1D's uncompiled full-body
wrapper/retry Result frontier. No Result erasure is promoted to event equality.

OriginalRetry: OPEN for the deployed source and all admitted prefixes. D163's
total owner describes complete terminating ordinary-error runs. `PV_L1E_OwnerJoin.original_run/original_prefix` CHECK the conservative embedding
in Logged, preserving all original ordered events, result and state.
`run_of_link` transports an independently supplied per-leaf SourceOwner link;
it does not construct that link for the deployed producer. Outer extraction fail/div,
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

## Additional checked composition and exposed mismatches

`PV_L1E_CallbackSafety` checks callback exclusion for all 49 composed logged
source interpreters, including Source069 and Source070, on outer errors and
divergence as well as normal returns. `PV_L1E_SourceEntries.attempt_entries`
DISCHARGES the prior model per-attempt-entry premise for this producer.
`successful_callbacks` and `all_outcomes` derive the exact returned count and
ordered `entryRange` for every model outcome. Native effects hidden by an
opaque Result lift still have no event credit.

`PV_L1E_OriginalSourceCount.same_original_success` CHECKS joint entered count,
rejections, account index attempts-1, proof-length upload arithmetic and one
statement upload, on the same source callback/store state, original owner,
proof and keys. It RETAINS `PV_L1E_OwnerJoin.PV_L1E_Link_SourceOwner`:
`∀ k s, sourceAttempt k s = liftOwner owner k s`. This is not native delivery
or completion of every retained operation.

`PV_L1E_SourceOwnerLinks.source_owner` uses the checked source erasure and two
explicit, OPEN Props to derive that unchanged SourceOwner definition:

- `PV_L1E_Link_OwnerControl`: for every k,s,
  `ProverRwRetryModel.attempt entropy pub compiled variant hash k s =
  SideChannelL1AttemptRecord.eraseOwner owner k s`.
- `PV_L1E_Link_OwnerEvents`: for every k,s,
  `(PV_L1E_RetrySource.attempt entropy pub compiled variant hash k s).events =
  (owner k s).1.events`.

Neither is instantiated for the original native producer. This is a checked
factorization of the remaining association, not discharge by repackaging.

The top-down check exposed two limits:

1. `PV_L1E_ErasureObstruction` CHECKS that identical Results need not have the
   same entry log, that identical native terminal values need not have the
   same COUNT log, and that an outer-failed source leaf cannot equal a lifted
   total D163 owner. These are mathematical interface countermodels, NOT
   honest-native leaks or counterexamples to the shipped implementation.
2. Attempt 66594 exposed Aeneas `Std.U8` versus Lean `UInt8` in the old upload
   helper's proof type. Attempt 66595 repairs the composition using the existing
   polymorphic count/rejection/account lemmas and the same length arithmetic.
   It does not identify those byte types or prove a native byte-image mapping.
   The early skeleton leaves `adapt` abstract and therefore did not itself
   test this byte conversion: its success certifies the stated algebraic
   interfaces, not a concrete source/native experiment instance.

The synthetic callback proof's failed tactic sources are retained at their
exact git revisions. A checked non-callback phase lemma and callee selection
by syntactic name replace inappropriate unfolding/case destruction; no
heartbeat, recursion, memory or timeout cap is raised. `generator-check`
validation is in `callback-safety-generator.json`. The unattempted
`drafts-PV_L1E_PrefixObstruction.lean.txt` has ZERO theorem credit.

The final combined statement, `PV_L1E_Statements.combined`, conjoins the exact
conditional COUNT input with runjoin's unchanged all-prefix native decoder
factorization. All four original trace links remain explicit. No concrete
native instance, simE law, or privacy conclusion is added by that conjunction.

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

**100/100 Lean starts: 92 pass, 8 fail. Zero native scopes, zero Kani.**
Only IDs 66500–66599 were used, with 66597–66599 reserved for final audits.
The accepted closure has 14 new source/model roots; `final-source-manifest.json`
separates those roots from the unattempted text draft. No compiler ran after
final validation and cache cleanup.

The three final checks passed:

| ID | Exact target | Exit | Wall seconds | Peak RSS bytes | Swaps | Source revision |
|---|---|---:|---:|---:|---:|---|
| 66597 | `PV_L1E_Statements` | 0 | 1.86 | 4408090624 | 0 | `58ee23d4a6e3863961f448df2c32da8ada904a1e` |
| 66598 | `PV_L1E_Axioms` | 0 | 1.67 | 4389330944 | 0 | `58ee23d4a6e3863961f448df2c32da8ada904a1e` |
| 66599 | `PV_L1E_FocusedReplay` | 0 | 1.67 | 4388814848 | 0 | `58ee23d4a6e3863961f448df2c32da8ada904a1e` |

Aggregate per-module wall time: **327.87 seconds**. Maximum
peak RSS: **4524724224 bytes**. Swaps: **0**. Every module has exact
source revision/blob/SHA, direct dependency fingerprint, command, exit, wall,
peak RSS, swap and original complete axioms output in `modules-ID.json`,
`receipt-ID.json` and hash-verified `raw/ID-00.out` / `.time`.
`axioms-summary.json` verifies all accepted printed declarations use only a
subset of propext, Classical.choice and Quot.sound. Failed elaborator-generated
sorryAx output is retained and earns no credit.

The 5,673 external objects were hash-verified BEFORE the first compile.
`reuse.json` verifies 814 pinned project objects and complete transitive
fingerprints. The 75 missing inherited objects were rebuilt privately because
L1D's cleanup removed its cache; no external module was rebuilt. Final
read-only validation checks **916 loaded project/own objects**,
**332 new direct dependency edges**, all **5673
external objects**, exact toolchain githash and inherited path prefix. All
match. Source authority remains EJR/freeze/h5 precedence and h6 checked cache
reuse; no h5'' substitution or XR import was used.

All Lean scopes used MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0,
TasksMax=64 and Lean -M7000, one scope at a time. Both immediate launch-admission
signals were checked in the same fail-closed shell command. Two aggregate
reservation refusals started NO compiler; the full 180-second cooldown was
observed and both IDs were ultimately reused under ruling (m'). The early
bookkeeping statement that refusals consume IDs was corrected. **Zero void
launches or ruling-(t) slips.** No host fault, memory kill, cap increase,
unchanged failed-source resubmission, local Lean build or native/Rust gate.

The generator's final `--check` passes and `source-preflight-final.json`
records no prohibited proof shortcuts, broad numeral normalization, or new
heartbeat/recursion settings. Symbolic callback lemmas replace the failed
proof search; the old 66.37-second failure and replacement remain recorded.
This is one final focused accepted-closure replay, not a full frozen privacy
release replay or proof of the deployed endpoint.

`COMMITS.txt` records the exact candidate-base to proof/audit-source-tip
commit range; the final evidence commit adds this report and receipts. No change under
crates/, programs/, protected soundness files, another worktree, shared compiler
objects, the observer or simE. No push, merge, ELF rebuild, timing measurement,
new Kani execution or quarantined Kani PASS consumption. Every evidence file
is below 20 MiB; no binary, compiler object or wallet/key material is committed.
`cache-cleanup.json` records removal only of this job's rebuildable objects and
links after the validated hash inventory; sources and receipts are retained.
All wallet/account keys remain untouched.

Stopped because the fresh **100-attempt budget is exhausted**. The next
concrete deliverable is `L1E_COUNT_NATIVE_ORIGINAL_SIME_JOIN`: construct the
actual source-world acquisition and client adapter, bind native callback/body/
world prefixes (including outer fail/div and Drop/unwind) to the SAME original
D163 execution, and supply its joint simE/failure coupling. Discharge the four
frozen trace links without redefining them. The now-checked source Result,
entry-order, and value/count composition are prerequisites, not that native
instance. No later input has been opened.
