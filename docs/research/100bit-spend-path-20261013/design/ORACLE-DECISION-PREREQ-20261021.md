# Oracle decision prerequisites, 2026-10-21

Scope: additive prerequisite modules on branch `codex/cx-oracle-prereq-20261021`,
base `26fc9ca35`. No endpoint port is authorised or performed.

Result: the independent-path strategy has exact B_V=1375 and safe compiled
bounds Q+1294 starts / Q+2750 log entries. Preserving Q+34 still requires a
terminal decoder theorem beyond initial-frame exclusion; preserving 1161
requires a shared multiproof implementation and correspondence. These are
the remaining decisions/obligations for a possible port, not hidden premises
claimed to have disappeared. Existing Lean modules, S-cone pins and the concurrent M10 instrumentation are untouched.

## Stage 1: issued queries

`OracleDecisionPrereqSampler` proves the uniform transcript allowance 115,
including malformed-message cases: row 0 costs at most 4, row 26 at most 4,
row 31 at most 17, and the other 30 rows at most 3.

`OracleDecisionPrereqPaths` constructs a terminal program that executes all
independent openings, compares their roots, and issues an explicit list of
additional frame/checksum reads. Its terminal count is exactly
`frames.length + sum (depth + 1)`; no acceptance, collision or distinctness
premise enters that count. The last node hash already computes the Merkle
root; comparing the supplied root issues no additional call.

For this explicit independent-path decision, the full verifier's closed
allowance is

`B_V(q, d, f) = 115 + 3*q*(d+1) + f`.

For 22 C1/C2/folded queries at binary depth 18 and the study's six
checkpoint/resume reads, `B_V = 1375 > 1161` (increase 214). Terminal calls
are exactly 1260, including 66 leaf hashes, 1188 parent hashes and six frame
reads. With no checkpoint/resume reads the allowance is 1369. The explicit
frame inputs are parameters, not a claim to have implemented the frozen
checkpoint writer/parser. The three commitment-frame hash calls are already
in the transcript allowance; parsed roots are values compared against the
last node digest. Roots are not double counted.

`OracleDecisionPrereqExact.verifier_exact` strengthens this to equality on
sampler-constructor-valid schedules: 115 transcript calls plus the exact
terminal
count. Thus 1375 is an attained issued-call count for this execution strategy,
not merely 33 times a worst-row bound. Root comparison failure does not
shorten this deliberate all-path program; early-stop implementations require
a separate prefix correspondence.

The smaller 1161 allowance requires shared multiproof execution and its
source/profile correspondence. Neither exists in the feasibility primitives;
independent path recomputation does not establish it. The new theorem bounds
actual issued calls, and hence distinct first reads of the original
experiment by `Q + B_V`, when the prover issues at most Q calls.

## Stage 2: decoder starts

The existing decoder counts recognised fresh *chain starts*, including
ordinary absorb addresses, not only canonical initialisation frames.
`BinInitialQueryAccounting.InitialisationCharging` explicitly labels
initialisation-only charging as an additional restriction which the endpoint
does not assume. The selected message codec enforces only a size bound.
Merkle leaves and nodes start with 16 and 18, whereas initial frames start
with 85; this proves they are not canonical initial frames. It is insufficient
to prove decoder rejection: the absorb parser inspects positions 32 and 33,
which contain unconstrained leaf/child bytes. No universal zero-start claim
is made from this first-byte separation.

`OracleDecisionPrereqStarts` reuses `BinHonestQueryBudget.rows_bound` and
proves exact compiler start preservation for arbitrary effectful decisions.
It gives `Q + 34 + N` if terminal starts are at most N, hence `Q + 34` under
an explicit zero-terminal-start condition. Unconditionally the independent
path/frame decision has `N ≤ 1260`, yielding **Q + 1294**. This is a proved
safe constant, not a claimed optimum. Arbitrary extra frame inputs can even
be recognised initial frames (`arbitrary_frame_can_start`, reusing
`BinDecoderInitialStarts.recognizes_initial`), so the feasibility interface
alone cannot assign all extra frame calls zero starts.

A production port retaining Q+34 needs a theorem about the actual parsed
terminal addresses and their chronological tables, or a different decoder
with a proved density/completion bridge. This work does not add such a
premise to an endpoint.

## Stage 3: recorded log and numeric envelope

`OracleDecisionPrereqLog` proves the exact compiler identity
`recordedLength = proverLength + 2*verifierLength` for the actual annotated
experiment with arbitrary word builder. Thus all runs, including accepted
runs, have length at most `Q + B_V + B_V`, or **Q + 2750** for this decision.
The replay offset is the full B_V, not the old transcript-only cost 115.
For a shared verifier eventually proved to cost 1161 the immediate bound
would instead be Q+2322.

`OracleDecisionPrereqObstruction` constructs accepted runs under a constant
oracle with a zero-query prover and log length at least 2520. It rules out
both the current Q+1161 premise and the attempted Q+1375+115 replacement for
this independent-path decision. `accepted_exact_log` gives equality 2750 on
sampler-constructor-valid accepted schedules and also refutes Q+1375+1161
at Q=0. M10 deliberately covers colliding accepted
runs too; collision exclusion cannot repair that cost premise.

The current `h_M10_log_length` therefore remains in its existing endpoint
signature. A future port can prove the analogous premise with Q+2750 only
after widening the extractor ledger's size restriction and rechecking its
polynomial cost envelope. Equivalently, the existing `Qledger + 1161` size
shape can be retained with `Qledger := Q + 1589`; the summary bridge proves
that reindexing, but establishing `LedgerRefinement e p (Q+1589)` and its cost
constant remains a ledger obligation. No concurrent instrumentation file is
changed.

`OracleDecisionPrereqNumeric` defines the proposed scalar envelope

`E(Q,c,B) = (Q+c)*15/2^109 + κ(Q+B) + 2^-126 + 2^-454`,
`κ(t) = 6*t^2/2^256`.

The collision argument becomes κ(Q+1375), irrespective of compiler replay
(the replay preserves distinct first reads). Keeping c=34 would increase the
gap to `(Q+1)*2^-100` by `6*214*(2*Q+2536)/2^256`. The unconditional c=1294
bound adds a further `1260*15/2^109`.

The proved sufficient ranges, with neighbouring endpoint failures checked,
are:

| Start allowance | Range for E ≤ (Q+1)*2^-100 |
|---|---|
| Q+34, conditional on zero terminal starts | 0 ≤ Q ≤ 14777960484892959601791002642008314224629686252 (old Qmax−428) |
| Q+1294, unconditional accounting | 39 ≤ Q ≤ 14777960484892959601791002642008314224629686214 (old Qmax−466) |

In particular the latter accounting does not establish the old assertion
beginning at Q=0: its numerical envelope already exceeds 2^-100 there. These
are scalar consequences, not an oracle-decision soundness theorem.

## Signature accounting and port estimate

No existing theorem signature changes. No premise removal is claimed; the
endpoint signature diff is empty. The eventual port remains unapproved.
`OracleDecisionPrereqSummary.prerequisites` combines all three bounds on
the same compiled experiment, with arbitrary word builder, oracle and prover,
without introducing query/start/log premises beyond the explicit prover
issued-query bound and opening/frame shape.

The original estimate remains **70–95 modules and 180–280 declarations**
for the active binary/canonical/R-wire/source API port. These prerequisites
supply reusable sampler, terminal count, compiler-start and log-length laws;
they do not make the carrier/threading work disappear. Allow roughly
**12–25 substantive proofs** after this work, with the rest mostly type
threading and erasure congruence. This is a source-inspection estimate,
not measured implementation labour.

The retained-Q+34 route still needs zero terminal starts on the constructed
full decision. Retaining 1161 also needs shared multiproof execution/profile
correspondence. Otherwise adopt 1375, the safe start constant 1294, the
changed numeric range and an extractor ledger covering Q+2750. Parsing the
real erased openings, malformed-schedule rejection, sampler-prefix legacy
transport, checked opening/word alignment and source/frozen/caller joins
remain. None is discharged by scalar counting.

Verification receipts are under `evidence/oracle-prereq-20261021/`.

## Verification

All eight new modules passed focused Lean 4.32 checks under the prescribed
`-j1 -M4400 -DElab.async=false` flags, private object overlay and shared
local lock. All 51 final theorem audits use subsets of
`{propext, Classical.choice, Quot.sound}`. No source contains proof holes,
new axioms, native decision procedures or resource-limit overrides.

| Target (`OracleDecisionPrereq` prefix) | Attempt | Exit | Wall seconds | Peak RSS bytes | Swaps | Theorems |
|---|---:|---:|---:|---:|---:|---:|
| `Sampler` | 2 | 0 | 4.798 | 3630694400 | 0 | 6 |
| `Paths` | 2 | 0 | 13.214 | 3643129856 | 0 | 8 |
| `Exact` | 1 | 0 | 7.928 | 3628630016 | 0 | 4 |
| `Starts` | 2 | 0 | 6.450 | 3635134464 | 0 | 10 |
| `Log` | 1 | 0 | 10.595 | 3618324480 | 0 | 5 |
| `Obstruction` | 3 | 0 | 32.679 | 3558752256 | 0 | 5 |
| `Numeric` | 3 | 0 | 23.070 | 3641638912 | 0 | 10 |
| `Summary` | 1 | 0 | 4.075 | 3623616512 | 0 | 3 |

There were 15 actual compilations: nine successful (one superseded
obstruction checkpoint) and six local elaboration failures. Every replacement
changed source; no unchanged compile was repeated. The failures were a
missing arithmetic close in the invalid sampler branch, path-module name/
association/distributivity fixes, a missing Table namespace in the start
module, rational-cast/cancellation rewrites in two numeric attempts, and a
local-let equality rewrite in the stronger obstruction. No memory failure
occurred and no cap was raised. Numeric proof warnings concern tactic
sequencing only.

Each attempt's packet retains exact argv/target, exit, wall, RSS, swaps,
source revision, source SHA256/snapshot, direct-import hashes/fingerprint,
full axiom lines and diagnostics. Source revision is the Git parent at
launch; exact working source is identified by its snapshot/hash. The audit
also records the parent revision of the final source inspection.

`audit.py` verifies every attempt's snapshot and receipt, every final source
against its green receipt, current direct-import hashes, complete theorem/
axiom-audit coverage, and that no pre-existing Lean module changed. The
manifest and audit are source/evidence validation, not an unchanged Lean
replay. These are focused cache-based checks, not a fresh coherent frozen
release build (D63). No certificate generator, package-wide build, SBF replay
or unrelated runtime suite was run. No production endpoint is changed.
