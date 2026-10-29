# L2E handoff — target not yet established

Branch: `codex/pv-l2e-20261029`; base: `67b128b900`.
Worktree: `/Users/dominic/ZK/.worktrees/pv-l2e` (sparse).
Host: `/home/dombarker/project-offloads/codex-pv-l2e-20261029/`.
No changes under `crates/` or `programs/`, no push, no keys/accounts created,
no funds moved or keys destroyed. `COMMITS.txt` contains the requested full log.

## Requested top theorem and unmet requirement

The instantiated native `PV_L2E.trace_simulatable` was NOT proved within the
first 15 attempts and remains unestablished. Attempt 67901 compiled only the
schema in `lean/PV_L2E_TraceMachine.lean`. Its statement is, schematically:

```
initial : honest i → good i → Related (realInit i) (simInit (pubData i) (coins i))
PV_L2E_Link_V353 ... ∧ ... ∧ PV_L2E_Link_V365 ... ∧ PV_L2E_Link_V367 ...
────────────────────────────────────────────────────────────────────────────
∀ n, tracePrefix native n (realInit i) =
     tracePrefix simulator n (simInit (pubData i) (coins i))
```

There are also explicit inherited V354, V357 and V360 links. Every link is a
standalone Prop about one transition's emitted events and the successor
relation (`StepLink`); none restates complete trace equality. However, the
machines, relation and initial-state/canonical-preparation association are
UNINSTANTIATED. The schema permits an arbitrary honesty predicate and coin
map; it cannot establish successful canonical preparation or D163. No native
whole-row claim follows merely from its name or from the links' names.
`AuditTop` prints the actual theorem types and link definitions.

`PV_L2E_CommonSample.on_existing_join` uses the SAME `join.cp.toR` and
`join.cp.toM`, and exactly `PV_FIB_Restricted.OffCharged old queries`.
It retains the canonical-initial-state and actual simE/D163 association gaps.
No independent tape, old-event change, new charge, acceptance conditioning,
new T item or observer/simulator weakening was introduced.

## Established mathematics and source limits

New owned-model proofs cover byte packing and lossless word casts; fixed byte
read/write indices; every direct reverse-division quotient store; every outer
remainder store; the complete quotient-array/list correspondence; positional
residues; the low returned quotient word and high zero slots; ascending carry
stores; fixed plans with bounds/divisor guards; canonical decoder checks and
unwrap safety; and gamma's complete cyclic increment value in both branches.
These are handwritten mathematical models, not extractor outputs. They do
NOT by themselves constitute a script-checked Rust-to-Lean structural binding.
In particular, native byte/array primitives, the flat source shift/OR expression,
field-record construction, wrapper call order and all circle/fallback paths
still need their complete source association. No b3p6-1 extraction claim is made.

The fuller query models retain all eager block/advance pairs, all 64 decoded
candidates (unused suffix included), the actual 18-bit mask, final-word success
and exhaustion, selected-advance bounds, and wrapper state on failure.
`HostQueryDetailed` adds the member loop guards, bounds checks, duplicate branch
and recursive calls omitted from the earlier event vocabulary. Its complete
Result agrees with `HostQuery`; a native complete-trace binding is still open.
The modeled scanner terminates by consuming input; exhaustion is never removed
from the Result domain. These helpers do not establish whole-row honest support.

`GuardedJoint.joint` proves an unconditioned good-event-weighted joint equality
for ACTUAL simE, an arbitrary observation of all middle coins, and challenge-
dependent finite tape permutations. The permutation is identity outside the
good domain; no resampling of rejected or unused middle coins is performed.
This is an equal-law theorem on the explicit product carrier, not an assertion
that that carrier is the native RunJoin sample. That association remains open.
The older `SimECoupling.full_coins_joint` fixes its coin parameter externally;
only `GuardedJoint` handles coin-indexed challenges in the stronger form.

The one native scope (before this relaunch) performed 76,304 finite complete-
state sampler/carry checks with literal copies of four source helpers and a
matched false control (exit 101). Rust 1.94.1, -O, overflow/debug assertions off,
source/toolchain/binary hashes are retained. This standalone harness is NOT the
full deployed crate configuration or shipped artifact; no whole-row credit,
singleton-input classification, Kani or extraction fidelity credit is claimed.

## Premise accounting and links

Every original `PV_L2_Premises.Vxxx` and `RustRealRefinement` premise is retained
unchanged. Before and after for each row remains:

```
∀ s, ¬ (∃ i, bad old queries i (join.cp.toM s)) →
 realRows (join.cp.toR s) .vxxx = modelRows (join.cp.toM s).1.1 .vxxx
```

No endpoint premise was removed, added or silently reassigned to trust.
`LINKS.md` gives each link's status, including V361–V365 and V367, whose whole
source/ambient association was not proved. The additional schema hypotheses
are explicit open proof parameters, not discharged deployment premises.
Allocation outcomes remain under rdea-1 only AFTER proving request sizes,
alignment and order; those whole-prover plans remain open. Compiler/runtime
preservation remains V370. Functions with random inputs or ambient transport,
hooks/workers are not misclassified under own-2'''. No checked honest-secret
leak was found; this is not a no-leak theorem.

## Validation and failure replacement

Budget exhausted: **100/100 Lean attempts** (58 focused, including 18 failures;
39 final replay targets; three audits), **1/30 native scopes**, **0/6 Kani**.
All 42 final targets pass. Peak accepted RSS 4,201,500 KiB; all-attempt peak
7,168,684 KiB (the replaced gamma failure); total swaps zero.
Final numbers are in `FINAL-VALIDATION.json`; all individual receipts record
target, source revision/SHA, exit, wall time, RSS, swaps and printed axioms.
The launch guard SHA is recorded there. It refuses an unchanged source SHA
from any prior failed attempt; no failed source was resubmitted unchanged.
Admission and allowed:true checks precede launch in the SAME shell command.
No known admission violation, refused launch or cap increase occurred.

67937 reached Lean's -M7000 kernel limit (7,168,684 KiB RSS; zero swaps).
It was NOT retried at a larger cap. The concrete gamma proof was replaced by
`GammaArithmetic.cyclic` over an ABSTRACT modulus (67938), then applied without
large normalization (67939, about 3.32 GB RSS and 1.34 s). Failed outputs,
including sorryAx/self references, are failure evidence only and never credited.
The final object check and fresh replay use the successful replacement.

The final preflight checked 6,199 object hashes in the resolved env-J cohort,
including all 5,673 external objects and reused L2D objects. Two early receipts
(67901 and 67902) lacked artifact hashes; their hashes were captured at preflight
and both objects were freshly rebuilt in the final replay, with equality checked
against the captured hashes. SimECoupling was reused unchanged and hash-verified.
There is ONE incremental final 39-target manifest and three combined audits;
this is not a replay of the entire deployed endpoint closure. Standard axioms
only are accepted. No local Lean builds, uncapped scopes or Kani runs occurred.

Next concrete deliverable: instantiate the detailed host transcript/scanner
machine and its canonical initial invariant on the EXISTING cp; bind every
raw block and advance, failed wrapper state and event prefix to the actual
simE/D163 coin history, then discharge V358. V356 still needs full sampler/
circle/fallback and call-order source binding. The native top theorem and all
remaining links are mandatory work, not cryptographic trust assumptions.
