# Prover commitment continuation 38

**Target not yet established.** Intended scope: D146 deployed statement image;
D143 public statement/proof bytes and adversary oracle answers; timing and
other side channels excluded. Intended headline trust list: P1 (shared
SHA-256 ROM), P7, TrustedStd, E1 (successful OS RNG draws), E2 (atomic
create-if-absent and persistence). No trust item is discharged or added here.

Task base: `23392f8056c0fd9d2376d147d7f5ecb97f033aba`.
Branch: `codex/cx-prover-commit38-20261022`. No shipped source changed.

## Stage 1: explicit reservation event and conditional counting

`ProverCommitReservationGuess38.reservationGuess` is the disjunction of an
adversary query matching the generated reservation input and a ledger entry
matching the reservation digest/path. `query_point` and `query_list` bound
query matches for a uniform nonzero nonce. `path_list` bounds ledger matches
for a fresh uniform digest. `fresh_slice` combines these as
`(Q + entries)/(2^256 - 1)` on the explicit product carrier.
`attempt_union` gives `(Q + entries)*attempts/(2^256 - 1)` from per-attempt
bounds without assuming independence among attempts.

These are fixed-context counting theorems, not an E1/native selected-nonce
or adaptive shared-ROM refinement. In particular, the uniform digest in
`fresh_slice` is a P1 fresh-coordinate calculation; it is not substituted for
a memoized answer. The necessary native sampler/history instantiation remains
open. No claim that an imported coupling hypothesis has been discharged.

J9152–J9155 are rejected elaboration drafts (finite/decision instance and
cast normalization); no resource failure or limit increase. J9156 compiles
all seven final top theorems: exit 0, wall 2.00 s, peak RSS 4,061,632 KiB,
zero swaps, axioms only [propext, Classical.choice, Quot.sound]. Every
attempt uses MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64 and
Lean -M7000. Source snapshots, source SHA-256, dependency fingerprints,
commands and full raw receipts are in
`evidence/prover-commit38-20261022/lean/attempts.json` and `lean/receipts/`.
Only new job modules are installed; changes to them are snapshotted before
replacement. No inherited shared source/object was overwritten.

## Stage 2: demonstrated numerical scope obstruction

The D148 interface has `Ledger := List OracleAnswer`,
`Action.additions : List Path`, and an independently chosen initial ledger.
Neither those definitions nor D150 bounds its length. `Q ≤ 2^64` in the
existing endpoint bounds oracle queries; it does not bound chosen path
entries or initial filesystem state. The binding security contract dated
2026-10-21 supplies no reservation-ledger entry budget either.

`ProverCommitReservationScope38.saturatedLedger` is a finite list containing
every digest/path, chosen without seeing any secret bytes. It is permitted
by the actual carrier. This list is defined symbolically; no concrete
universe was enumerated or evaluated. `saturated_guess` and `saturated_mass`
prove reservationGuess holds pointwise and has mass 1 for arbitrary query,
nonce and address maps, including any P1 oracle and any E1 nonce law.
`saturated_duplicate` follows the actual ledger reserve definition and shows
every path returns Duplicate, for every byte-blind fault schedule. E2 is
consistent with this case. This is a mathematical model counterexample, not
a practical storage attack or a claim that privacy fails: the duplicate
error is witness-independent and can be coupled exactly.

`no_unrestricted_numeric` independently disproves
`∀ entries, budget 0 entries 1 < 2^-100`: already entries = 2^256−1 makes
the charge 1. Thus the demanded addition of the whole reservationGuess mass
cannot yield a uniform <2^-100 headline over the unrestricted D148 ledger
carrier. There is no corresponding problem with the parametric counting
inequality itself; large entry counts correctly give a large upper bound.

`bounded_charge` proves that IF Q and entries are each ≤2^64 and attempts
≤128, the per-side reservation charge is ≤2^-180. `bounded_total` proves
that adding twice that charge to the existing conservative numeric expression
still gives <2^-100. The factor two accounts for real and simulator sides.
128 is a conservative arithmetic envelope (16 draws × 8 attempts); it is
not a theorem that the source makes 128 reservation calls or a discharge
of the selected-nonce law. The new entries hypothesis is explicit and is
NOT inserted into the deployed endpoint. Its use there needs an announced
scope/work-accounting decision or a different coupling argument.

J9157 is a rejected finite-instance elaboration draft. J9158 compiles all
eight final top theorems: exit 0, wall 2.18 s, peak RSS 4,172,632 KiB,
zero swaps, axioms only [propext, Classical.choice, Quot.sound]. The numeral
454 warning comes from the inherited dyadic expression; no exponentiation,
recursion or heartbeat threshold is raised. The generic list-membership
lemma avoids elaborating concrete finite universes.

## Stop and exact next interface

Per the requested obstruction stop rule, this job stops after the proved
scope mismatch. The next required interface is a resource-accounted
adversarial environment:

- a named bound covering the initial ledger AND every adversarial addition
  over every permitted execution prefix, with its relation to the existing
  work/query budget proved and preprocessing charged; or
- a memo/ledger-preserving real/simulator coupling that handles ledger
  collisions exactly, so the whole reservationGuess event need not be
  charged as a small error for unrestricted ledgers.

Recommended direction: first decide whether ledger entries are charged to
an existing work budget; do not infer entries≤Q from byte-blindness. If the
unrestricted-ledger quantifier is retained, couple witness-independent
membership errors rather than charging every membership hit. Either route
must preserve the full query history, selected nonzero nonce law,
sixteen-draw failures and eight-attempt control, E1/E2, and arbitrary
byte-blind schedules. No shipped change is needed to exhibit the obstruction.

The complete native simulator publication (proof bytes, ordered tables,
merge, early errors), D143 source-to-FSExperiments conversion, concrete
shippedProverExperiment, both WholeRunJoins and removal of
RustProverRefinement remain open. The fresh-slice counting lemmas are not
misreported as completing those interfaces or reservation memo transport.
No active headline theorem is changed. The numerical target is unchanged.

## Visible numeric before/after (conditional arithmetic, not an endpoint)

Before, verbatim from ProverCommitFuelMass22:

```lean
theorem total_lt_target {q r : Nat} (hq : q ≤ 2^65) (hr : r ≤ 2^64) :
    1 / (2 : ℚ)^109 + 1 / (2 : ℚ)^137 + 1 / (2 : ℚ)^454 +
      QueryScanFreshUnion.freshBudget q + 2 * ProverCommitSeedEvent19.budget r +
      2 * charge < 1 / (2 : ℚ)^100
```

After, verbatim from ProverCommitReservationScope38:

```lean
theorem bounded_total {scan q entries attempts : Nat}
    (hs : scan ≤ 2^65) (hq : q ≤ 2^64) (he : entries ≤ 2^64)
    (ha : attempts ≤ 128) :
    1 / (2 : ℚ)^109 + 1 / (2 : ℚ)^137 + 1 / (2 : ℚ)^454 +
      QueryScanFreshUnion.freshBudget scan + 2 * ProverCommitSeedEvent19.budget q +
      2 * ProverCommitFuelMass22.charge + 2 * budget q entries attempts <
        1 / (2 : ℚ)^100
```

The added `he` is why this cannot replace the unrestricted headline.
The D150 term remains visible; it has not been absorbed into seedGuess,
fuel, E1/E2 or another existing allowance.

## Active endpoint before/after: unchanged

The active theorem still quantifies `x : Statement K CommitHandle` and an
independently supplied `rust : FSExperiments ...`, with
RustProverRefinement explicit. No D146 domain restriction, environment or
entry budget has been silently installed. Exact surrounding binders and
TrustedStd are retained in `endpoint/` before/after snapshots (empty diffs).

Before:

```lean
theorem privacy_headline_deployed
    (refinement : RustProverRefinement template outputs x rust observer_program)
 :
    ZK_FSS h B outputs rust x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x)
      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge < 1 / 2^100
```

After:

```lean
theorem privacy_headline_deployed
    (refinement : RustProverRefinement template outputs x rust observer_program)
 :
    ZK_FSS h B outputs rust x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x)
      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge < 1 / 2^100
```

## Final verification and handoff

J9159 is the final focused audit of all fifteen new top theorems and their
new-module dependency closure: target `R1Z.ProverCommitReservationAudit38`,
exit 0, wall 1.65 s, peak RSS 4,131,160 KiB, zero swaps. Every audit contains
only [propext, Classical.choice, Quot.sound]. The source revision is the
recorded task base plus the exact retained source overlay and transitive
object fingerprints. `final-proof-audit.json` verifies the final host sources
against the local sources at checkpoint `0734a2eaa` plus the retained audit
module overlay, and checks every audited dependency object; all match.

All eight attempts J9152–J9159, including rejected drafts, have exact targets,
commands, source snapshots/SHA-256, dependency fingerprints, exit statuses,
wall/RSS/swap and full axioms/diagnostics retained in
`evidence/prover-commit38-20261022/lean/attempts.json`. No unproved declaration
is used by an accepted result. No forbidden proof shortcut or increased
recursion/heartbeat limit was introduced. `git diff --check` passes.

All 491 tracked crates/programs files match the actual base byte for byte;
`shipped-sources-unchanged.json` records size and SHA-256 for each. The
shipped-file rule therefore triggers no ELF rebuild. No native/Kani, Aeneas,
Rust, SBF or unchanged runtime regression ran. Prior evidence is reused
without claiming a new source refinement. No full frozen manifest replay
ran because native reservation/history preflight and the numerical-scope
interface remain open. This is not a formal release result.

No binaries, objects, ELFs, tarballs or local target directory are added.
No wallet/account keys were created, deleted or altered. All compilation
jobs are finished. No push or merge was performed.

Checkpoints: `c27158951` (event/counting), `0734a2eaa` (scope obstruction and
conditional numerics). Next unused assigned Env J attempt: **J9160**.
The security target remains **not yet established**.
