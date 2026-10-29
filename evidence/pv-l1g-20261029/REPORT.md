# L1G count links — D476

Branch `codex/pv-l1g-20261029`, candidate `873ff1cc6a`, exact sparse worktree
`/Users/dominic/ZK/.worktrees/pv-l1c`. No push or merge.
**Target not yet established. None of the four full native links is closed.**
The headline-carrier question remains with pv-fib; it changes none of these links.

## Checked progress and remaining native inputs

`PV_L1G_WorldRetry.run` composes independently supplied full-world leaves.
It retains their calls with their pre-world annotations and threads their actual
post-world through retries. `failure_prefix` and `divergence_prefix` preserve
both calls and post-world; `retry_calls` preserves earlier calls even if the
suffix fails or diverges. `valid_run` transports pv-own's transition relation
from individual leaves; it does not supply native allocator/OS adequacy.

`logged_join` relates that full-world execution to the inherited logged retry,
carrying the successful final world in its state. This is an auxiliary
projection: the full Run is retained independently, including failure worlds.
`reached_congr` proves full Run equality from equality of full-world leaves
only at normal retry-reachable states. It handles outer failure/divergence
without requiring terminating leaves. `PV_L1G_BodyBind.bind_at` provides the
corresponding full-world composition rule at a reached continuation value.
No lifted Result is promoted to a silent native leaf.

`original_logged` consumes the unchanged pv-diag10 reach criterion and the
original reached-owner association. `PV_L1G_OriginalRetry.original_retry`
concludes EXACTLY the unchanged `PV_L1E_Link_OriginalRetry`, given that leaf
association, the body/world interpretation, and the client adapter. This
conditional criterion constructs none of those native inputs. In particular,
the total D163 owner does not represent an outer-failed/divergent leaf merely
because the generic full-world recurrence can retain such a prefix.

`PV_L1G_CountPrefixes` proves count and rejection accumulation through source
world composition, retaining all earlier entries on outer failure/divergence.
`PV_L1G_SourcePublication.actual_count_with_prefix` combines those independently
retained source calls with the ACTUAL extracted RetriedProof.attempts.val read,
using the existing returned-output laws. The prefix encoder is an explicit
source operation input, still requiring deployed leaf adequacy. It is not a
native decoder projection or an installed all-prefix acquisition instance.

| Frozen link | Status | Concrete residual |
|---|---|---|
| `PV_L1E_Link_CountAcquisition` | PARTIAL; full link OPEN | Acquire the actual earlier ordered native count/rejection word into the independent source Run, with a bound leaf encoder for every admitted terminal/prefix. |
| `PV_L1E_Link_BodyWrapper` | OPEN | Bind every body/callback/checker leaf, Drop/unwind, abort and client wrapper to its full source world and ordered calls. Complete Result erasure does not supply those effects. |
| `PV_L1E_Link_OriginalRetry` | PARTIAL; concrete link OPEN | Reached full-world/owner leaf association and actual client/world adapter. The exact frozen link now has the world-threaded sufficient criterion above. |
| `PV_L1E_Link_NativeD163` | OPEN | Associate the SAME original D163 execution with the native trace/world/terminal, and prove its joint original/simE/failure law. |
| `PV_DIAG10_Link_Sites` | OPEN, included with NativeD163 | Joint honest occurrence/variant/site law on the same public/coin/history context and exact charged failure event. No new instance or distributional law is claimed. |

The unchanged body frontier still has 15 opaque Result lifts in Source070 and
43 in Source069, besides their named producers. `source-preflight.json` checks
all frozen Link files against the candidate, including Sites. The reused
structural retry/callback binding is hash-rechecked in `retry-source-reuse.json`;
its leaf/Drop/unwind, entropy-failure independence and plan/main residuals remain.
V370 remains at the owner's pending D381/D386 compiler-cohort boundary.
V394 account selection at attempts−1 and the upload/operation count association
remain obligations of the actual client adapter; the returned field read and
numeric guards do not discharge them.

## Composition and premise accounting

`PV_L1G_Statements.combined` concludes precisely the typed
`PV_RJ4IDB.OpenInputs.L1_COUNT_TRACE actualCount native`, conjoined with the
explicit unchanged Sites hypothesis and the inherited lossless all-prefix
factorization. All four original trace links and Sites remain separate
hypotheses. No observer, simulator, witness restriction, failure event or
trust field was changed. T remains exactly entropy_law, entropy_kernel,
observation. Headline/deployment premises removed/added/weakened/changed:
**0/0/0/0**. V347–V351 remain OPEN/P.

L1_COUNT_TRACE remains PARTIAL. ORACLE_PREFIX, TIME_TRACE and
RETAINED_SIDECHANNELS remain OPEN; ORACLE was not started because COUNT did
not close. Allocation, addresses, clocks, durable/environment effects and
cross-channel order remain retained. D359 remains pending wherever a full
joint duration law invokes the throttled-host measurements. No honest-native
secret-dependent leak or shipped-source counterexample was constructed.

## Validation and object reuse


**99 Lean starts: 95 pass, 4 fail. Zero native scopes; zero Kani.**
All 100 assigned IDs are consumed: 67636 was refused before any compiler
started, so it costs zero Lean attempts but cannot be reused. The 100-start
budget cannot be completed inside this fixed 100-ID block. No out-of-block ID
was used. The three reserved checks all passed:

| ID | Exact target | Exit | Lean wall seconds | Peak RSS bytes | Swap | Source revision |
|---|---|---:|---:|---:|---:|---|
| 67697 | `PV_L1G_Statements` | 0 | 1.87 | 5110493184 | 0 | `724872bd1ce057d4478432f3bdc1efd985d13085` |
| 67698 | `PV_L1G_Axioms` | 0 | 1.71 | 5090422784 | 0 | `724872bd1ce057d4478432f3bdc1efd985d13085` |
| 67699 | `PV_L1G_FocusedReplay` | 0 | 1.71 | 5091393536 | 0 | `724872bd1ce057d4478432f3bdc1efd985d13085` |

Aggregate compiler wall time: **182.29 seconds**. Maximum peak
RSS: **5110493184 bytes**. All scopes used MemoryHigh=6G,
MemoryMax=8G, MemorySwapMax=0, TasksMax=64 and Lean -M7000, one at a time.
There was one immediate admission refusal on a vanished unrelated service
cgroup, followed by the complete 180-second cooldown and the NEXT unused ID.
No compiler ran on the refusal; no void launch, cap increase or resource kill.

Failures were 67614 (ambiguous bind reduction), 67615 (redundant closing
rfl), 67616 (a documentation comment before #print), and 67622 (remaining
projection reduction). All replacements changed and committed their source
before submission. Accepted replacements are 67617 and 67623; original logs,
source hashes and revisions remain. Failed-elaboration sorryAx earns no credit.
`failed-source-replacements.json` checks the changed-source replacements.

The requested older host directories l1c/l1d/l1e/l1f contained **zero compiled
objects**: their committed cleanup receipts had removed them. This absence
is recorded, not silently counted as reuse. All **1,665 surviving compatible
objects** were reused read-only: 1,640 from the pinned runjoin cohort, plus
25 diagnostic/decoder objects. Their selected source hashes, every import's
object fingerprint, toolchain and effective object prefix were checked before
use. Only 81 missing inherited prerequisites were rebuilt, unchanged and
privately, to connect the new rules to the actual source/retry definitions.

Final read-only validation checks **1759 project/own
objects**, **4095 dependency edges**, and all
**5673 external objects**, with exact toolchain
`8c9756b28d64dab099da31a4c09229a9e6a2ef35`. All match. EJR/freeze/h5 precedence remains;
no XR import, source substitution, shared-source or shared-object overwrite.
The effective LEAN_PATH is recorded in `final-validation.json`.

All 18 new helper theorems and the combined statement are covered by the
accepted axioms audit; every accepted axiom set is a subset of
{propext, Classical.choice, Quot.sound}. Each receipt and modules record
retains the exact target, command, exit, wall, peak RSS, swap, source
revision/blob/SHA, dependency fingerprint and full axioms output. `raw/`
contains the hash-verified original compiler/time output. This was one final
focused replay; no unchanged frozen privacy release regression was repeated.

The verified host objects are retained as a pinned reuse cache, with
`CACHE-PIN.json` referencing this final validation, to support the user's
explicit reuse requirement and AGENTS resource rule 6. No compiler objects,
binaries or files over 20 MiB are committed. No cargo/extractor scratch was
created. All sources, receipts and keys are retained.

Stopped at exhaustion of the assigned ID block. The next deliverable is a
statement-by-statement native leaf/world producer and actual earlier
count/rejection acquisition on the SAME original experiment, followed by
the exact joint simE/failure/site law. The conditional retry bridge does not
manufacture those missing inputs.

`COMMITS.txt` records the complete candidate-to-proof/audit-source-tip range.
No change under crates/ or programs/, protected soundness files, another
worktree, observer or simE; no push, merge, ELF rebuild, timing measurement,
Kani run, wallet/key/account operation, or new trust item.
