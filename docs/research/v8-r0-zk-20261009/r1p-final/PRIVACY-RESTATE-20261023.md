# Privacy endpoint restatement audit, 2026-10-23

Branch `codex/cx-priv-restate-20261023`; inspected revision
`235da438aa136271c0380b2f8f2acf57203ea032`. **Stopped on item 2's equivalence
condition; target not yet established.** No new endpoint is claimed proved.
Read the binding AGENTS.md security/proof rules, common worker rules,
LOG D42–D68 and D184, and the actual endpoint definitions.

## Stage 1: conclusion audit and explicit stop

D184 correctly identifies a sufficient route to the standard simulation
claim: couple deployed real execution to model real execution, then use the
proved model comparison to the mathematical ideal simulator. Native
`sim.rs` correspondence is unnecessary for that new comparison. However,
this is a different theorem from the current **fixed-experiment** conclusion.
The requested equivalence cannot be asserted for its actual quantifiers.
This finding does not invalidate privacy of the deployed prover.

`FSExperiments` independently supplies `real`, `ideal`, and `observe`.
`ZK_FSS` does not existentially quantify over an ideal implementation and does
not identify it with the mathematical game. Its conclusion expands to:

```lean
∀ (adv : rust.Adversary) (w : h.Instance), h.public w = x.1 →
  |mean (realTest h B outputs rust adv x w) -
    mean (idealTestS rust adv x (simE h.transport B outputs x))| ≤ ε
```

The proposed comparison instead is (explanatory notation, **not an added
or compiled declaration**):

```lean
∀ (adv : rust.Adversary) (w : h.Instance), h.public w = x.1 →
  |mean (realTest h B outputs rust adv x w) -
    mean (idealTestS source (RomObserverBin.observerMap rust observer_program adv)
      x (simE h.transport B outputs x))| ≤ ε
```

Let the three means be R, I_rust, and I_source. The old conclusion says
`|R - I_rust| ≤ ε`; the proposed conclusion says `|R - I_source| ≤ ε`.
Holding every real-side field fixed and changing only `rust.ideal` leaves
the proposed proposition, model theorem, and conjunct 1 unchanged, but can
change the old proposition. At the scalar level, R = I_source = 0 and
I_rust = 1 satisfy the proposed bound and violate the old one for ε < 1.
These are legitimate Boolean experiment probabilities. The FSExperiments
interface imposes no law preventing the ideal field from ignoring its
simulator argument. This is a counterexample to a general equivalence
argument, not a constructed attack on the selected model or a claim that
its concrete distribution has those particular means.

The current second join bounds the missing `|I_rust - I_source|` term;
it does not give exact equality either. Removing it while retaining the
same old conclusion is unsupported. A triangle inequality with nonzero
ideal discrepancy is not a same-ε biconditional. Changing only the benchmark
is a valid way to state the intended deployed simulation property, but is
not a literal premise removal from the existing theorem. Under the explicit
instruction to stop if the conclusions are not equivalent, no new Lean
module, wrapper, or compile is submitted. Recommendation to the lead:
explicitly approve a **different composed simulation theorem** with the
mathematical ideal as its fixed benchmark, retaining the old theorem as-is.
That needs no deployed native Rust simulator. It does not require weakening
the adversary or security target.

## Quantifiers, observations, error and efficiency

The existing declaration is universal over `CommitHandle`, `Aux`, `template`,
`outputs`, public `x`, `rust`, and `observer_program`; internally over every
`adv` and every honest instance `w` with `h.public w = x.1`. It uses the
fixed admitted builder. The proposed comparison need not change any of
those quantifiers. In particular it must not silently install the D146
source-representable statement domain or identify arbitrary `Aux` metadata
with unit. Neither concrete deployed instance nor real join is supplied.

The real observable stays the entire ROMView and Boolean decision. The
observer map keeps `rust.observe adv` as its decision function; its adaptive
query program is supplied by `observer_program`. The model retains its
existing query fuel, query order, repeats, early exits and oracle answers.
The ideal random carrier changes from `rust.IdealRand` to
`source.IdealRand`; the ideal experiment and source observer interpretation
change accordingly. A real-only endpoint should not need finite/nonempty
instances for `rust.IdealRand`. Those are real changes to the statement,
even though the deployed real observation is untouched.

The current fuel endpoint's exact envelope is
`modelError W Pr L₁ L₂ + 16/2^486 + freshBudget (8*n1 W Pr+1)
 + 2*seedBudget (2^64) + 2*fuelCharge`.
Its conclusion also gives the displayed numeric upper bound and `< 2^-100`.
A one-join triangle uses only the real mass, seed and fuel charges, so it
could conservatively retain this entire envelope without new charges.
This arithmetic sufficiency does not prove equivalence of the benchmarks.
The old seed-only endpoint omits the two fuel charges and has the same
benchmark issue. The exact fuel statement is reproduced below.

Efficiency of the new benchmark would concern mathematical simE **and its
whole ideal game**, not whether the never-deployed Rust cost probe matches
it. The cost passes prove conditional run equality/relative bounds; the
latest `SIM-COST7-20261022.md` expressly leaves concrete public/metadata
selection, exact Boolean P_R1, full representation costs and a numeric
preparation certificate open. It would be inaccurate to report an
unconditional concrete simE cost bound as established. No such assumption
is discharged or added by changing the benchmark.

## Verbatim before and retained after

Both snapshots are extracted from
`lean/R1Z/ProverCommitDeployedFuel22.lean`, with the module's unchanged
surrounding variables and local notations. They are verbatim declaration
headers, excluding proof bodies. `privacy-restate-20261023/audit.py` checks
them against the actual source; the retained after is identical because the
stop condition prevents installing the proposed different conclusion.

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

After (retained unchanged; no new endpoint):

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

## Stage 2: remaining real-side obligations

Pending independent source-obligation map.

## Validation and handoff

Pending final source audit. No Lean or Rust compiler has run; J10800–10899
are unconsumed. No shared host source/object was read or overwritten.
