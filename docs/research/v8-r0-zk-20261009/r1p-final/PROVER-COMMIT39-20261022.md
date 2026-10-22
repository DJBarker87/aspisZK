# Prover commitment continuation 39

**Target not yet established.** D151 scope: deployed statement image (D146),
public statement/proof bytes and adversary oracle answers (D143); timing and
other side channels excluded. Trust items remain P1, P7, TrustedStd, E1, E2.
No new cryptographic or environment assumption is added.

Task base: `561dcef39ae048ca4baeaad40a3e2bf7fd704d10`.
Branch: `codex/cx-prover-commit39-20261022`. Stopped on the source nonce-ownership finding below.

## Stage 1: source ordering and exact ledger coupling

Read D143–D151 before changing the proof. The actual secure wrapper
`prove_masked_retrying` (prover.rs:327–334) obtains secrets using
`StateOnlyAttemptSecrets::generate`, with no witness argument. The generator
(state_only_entropy.rs:172–194) draws 96 bytes and selects only by nonzero
checks on the three blocks; no witness enters this selection. The public
context and binding (prover.rs:106–115) use public bytes, variant and nonce.
`prove_masked_with_attempt` reserves/builds at line 129 before its first
read of the compiled witness trace at line 132. Within the builder,
state_only_entropy.rs:392–447, reservation at 408 precedes entropy expansion.
The reservation path (901–916) hashes only the fixed reservation domain and
nonce and appends its hexadecimal encoding plus `.burn` to the wallet ledger
directory. Neither statement digest nor private seed nor compiled trace enters
the path. The statement digest is written only after successful create.

On an occupied path, native `AlreadyExists` returns `Ok(false)` (934), the
builder returns `ReusedMaskNonce`, `mask_error` maps that to `Error::Semantic`
(prover.rs:172–177), and the retry owner aborts (371–374). It does not consume
another proof attempt or publish proof bytes. Byte-blind create/write/fsync
faults remain environment behaviour rather than a probability charge.

This source argument concerns the concrete OS-generated wrapper. The generic
`prove_masked_retrying_with` callback and `generate_for_mask_nonce` do not
establish a uniform independent nonce for an arbitrary caller; no universal
claim about such caller-supplied nonces is made.

`ProverCommitLedgerCoupling39` proves full state equality for the shared
reservation transition and preparation prefix; collision after injected
additions implies duplicate; duplicate preparation prevents either real or
ideal continuation from running. Both error and retained environment state
coincide. The theorems quantify arbitrary finite ledgers and schedules,
with no ledger cap and no collision probability term. They are model-prefix
laws, supported by the source-order inspection above, not a complete
source-to-FSExperiments conversion or a successful-continuation join.

J9160–J9161 were rejected elaboration drafts (ambiguous opened names, then a
qualified secret alias). J9162 compiles the four final prefix theorems:
exit 0, wall 1.85 s, peak RSS 4,151,728 KiB, zero swaps; axioms only
[propext, Classical.choice, Quot.sound]. The exact source overlay, dependency
fingerprint and raw receipts are retained in the part 39 evidence directory.
Only this job's new module was installed; earlier drafts of it were snapshotted
before replacement. No inherited shared module/object was overwritten.

## Demonstrated source obstruction: preselected deployed nonce route

**The D151 source premise is not established for the complete advertised
secure API.** The safe OS-generated wrapper above is only one route. The
same source explicitly documents another deployed route:

```rust
    /// A deployed proof binds this nonce to the proof-account address. Clients
    /// therefore generate the account keypair first and pass its public key
    /// here. The public nonce only needs to be unique; both secret seeds still
    /// come independently from the operating system and are zeroized on drop.
```

`StateOnlyAttemptSecrets::generate_for_mask_nonce` (state_only_entropy.rs:
202–224) accepts the caller's 32-byte nonce, rejects only zero, then draws
**64** bytes for field entropy and leaf seed. It never samples the nonce or
checks its origin. `prove_masked_retrying_with` (prover.rs:354–375) accepts
an arbitrary `next_attempt` callback, documented at 337–341 as supporting
this proof-account route. Neither callback signature nor nonce guard implies
independence from a caller's witness, nor uniformity on all nonzero 256-bit
strings. E1 concerns successful OS draws and cannot supply a missing law
for an input that is not drawn by that API. E2 and P1 do not fix that gap.

The target history confirms that this is relevant, rather than an unrelated
optional API: D38.4 binds the nonce to a fresh proof-account keypair; D141
names the real-side `prove_masked_retrying_with` owner. The LOG randomness
inventory explicitly records preselected proof-account public keys and
excludes the alternate 96-byte `generate()` adapter.
`HONEST_PROVER_EXPERIMENT.md:18–24` does the same. These historical experiment
documents are used for the nonce-source choice only, not to override later
D143 observable or protocol rulings. No later read ruling supplies a
source theorem changing that ownership to `generate()`. The exact account
setup/public-envelope transport remains open in that document. It would be
incorrect to silently substitute the 96-byte wrapper and report the deployed
nonce obligation closed.

There are two separate consequences:

- A caller may choose between two nonzero nonce inputs using a witness bit.
  Both pass the actual input guard. Thus independence cannot be proved for
  arbitrary callers merely because the callee has no witness argument.
- Even an independently chosen fixed nonce can be public/known beforehand,
  as permitted by the preselected public-address interface. One adversary
  query at its reservation input is then a prior memo hit on every successful
  generation. It obeys the existing Q cap. No ledger entry, ledger cap,
  fault, seed leak or timing observation is involved. This is a counterexample
  to the requested memo *bound*, not a claim that such a query breaks privacy.

`ProverCommitPreselectedNonce39` retains these facts symbolically:
`known_memo`, `known_mass`, `not_requested_bound`, `supplied_depends`, and
`distinct_create`. The latter shows why changing a witness-selected nonce
need not preserve the duplicate outcome in a fixed private ledger.
`first_success_lower` and `raw_E1_exceeds` keep the uniform first raw 64-byte
seed draw: success has mass at least `1 − 2/2^256`, and the memo-hit mass on
those successes already exceeds `budget (2^64) 128`. Later RNG retries need
not be omitted or conditioned away; they can only add successes. The byte-blind
schedule can be the all-success schedule and the ledger can be empty.

The source evidence is read-only inspection, not an executable Rust proof:
`nonce-source-audit.json` records SHA-256, exact line excerpts and the source
revision; `harness/source-audit.py` reproduces the pins. The Lean counterexamples
are on the explicit finite carriers. They are not mislabelled as a Charon/Aeneas
extraction of the entire API.

Per item (1)'s instruction to stop on a source finding, the later native
publication, source-to-FSExperiments conversion, shippedProverExperiment,
both concrete WholeRunJoins and endpoint premise removal are not attempted
past this obstruction. No native-source change or silent API/domain
restriction is installed.

## Conditional memo arithmetic retained, not a deployed bound

While checking the callers, the requested arithmetic was prepared separately.
`ProverCommitReservationMemo39.prior_mass` proves Q/(2^256−1) on a uniform
nonzero nonce independent of its prior query list. `context_mass` permits the
list to depend on arbitrary earlier contexts, but the fresh nonce is a separate
coordinate. `attempts_mass` gives Q·attempts/(2^256−1) without independence
among attempt events once their individual laws are supplied. No ledger
term or entry hypothesis occurs. `bounded_charge` and `total_lt_target`
prove the requested numerical inequality at Q≤2^64 and attempts≤128.
These facts do **not** prove the false instantiation for arbitrary
preselected nonces. No reservation query/history transport into the actual
FS experiment is asserted, and no active headline theorem was weakened
or renamed to hide its outstanding source correspondence.

The 128-draw arithmetic envelope covers 16 raw candidates times eight
attempts; it is not a claim that 128 reservations occur. There are at most
eight source reservations. Charging fewer attempts does not resolve the
known-nonce counterexample, which already occurs with one prior query and
one source attempt.

## Verbatim numerical before/after (conditional arithmetic only)

Before, ProverCommitFuelMass22:

```lean
theorem total_lt_target {q r : Nat} (hq : q ≤ 2^65) (hr : r ≤ 2^64) :
    1 / (2 : ℚ)^109 + 1 / (2 : ℚ)^137 + 1 / (2 : ℚ)^454 +
      QueryScanFreshUnion.freshBudget q + 2 * ProverCommitSeedEvent19.budget r +
      2 * charge < 1 / (2 : ℚ)^100
```

After, ProverCommitReservationMemo39:

```lean
theorem total_lt_target {scan q attempts : Nat}
    (hs : scan ≤ 2^65) (hq : q ≤ 2^64) (ha : attempts ≤ 128) :
    1 / (2 : ℚ)^109 + 1 / (2 : ℚ)^137 + 1 / (2 : ℚ)^454 +
      QueryScanFreshUnion.freshBudget scan + 2 * ProverCommitSeedEvent19.budget q +
      2 * ProverCommitFuelMass22.charge + 2 * budget q attempts <
        1 / (2 : ℚ)^100
```

The additional term is visibly `2 * budget q attempts`, one charge per world.
There is no ledger term or bound. This arithmetic theorem cannot be substituted
for a deployed nonce law, which is contradicted for the preselected API above.

## Verbatim active endpoint before/after: unchanged

The full surrounding binders and body are retained in identical
`endpoint/before.lean.txt` and `endpoint/after.lean.txt` snapshots.
`x : Statement K CommitHandle`, arbitrary `rust : FSExperiments ...`, and
`RustProverRefinement` remain as before; no D146 specialization, nonce-source
restriction, query restriction, new environment premise or error term has been
silently installed.

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

## Exact next interface and stop

The next required interface is the **deployed proof-account nonce source and
reservation-history owner** at
`generate_for_mask_nonce(mask_nonce)` → `prove_masked_retrying_with(next_attempt)`.
It must identify the source account-key generation, which values the adversary
knows before reservation, how setup and prior queries are represented, and
how that public nonce is coupled across both worlds. E1 for the private 64-byte
seed draw cannot substitute for this interface.

Two possible repairs require a lead ruling: explicitly select the 96-byte
OS-nonce wrapper as the deployed target and prove the actual call path uses it;
or retain the proof-account route and provide a memo-preserving coupling
that handles known/public reservation inputs exactly. The latter is the
recommended direction for the presently documented deployed route. Changing
only the denominator or adding a ledger cap cannot repair a known-nonce hit
of mass near one. No such target/scope change or new assumption is made here.

The remaining native simulator publication and source-to-FSExperiments
conversion, concrete shippedProverExperiment, both WholeRunJoins and deletion
of RustProverRefinement remain open. This is the requested obstruction stop,
not a claim that their current conditional wrappers close the implementation.

## Focused verification

J9167 compiles all six conditional memo/counting/numeric theorems: exit 0,
wall 2.17 s, peak RSS 4,077,760 KiB, zero swaps. J9170 compiles all eight
source-interface counterexample/support theorems: exit 0, wall 2.15 s,
peak RSS 4,170,348 KiB, zero swaps. All printed axioms are subsets of
[propext, Classical.choice, Quot.sound]. No recursion, heartbeat or numeral
reduction limit was raised. The inherited dyadic exponent warning is not a
resource failure.

J9163, J9165–J9166 and J9168–J9169 are rejected elaboration drafts, retained
with source snapshots and diagnostics. The replacement for the complement
mass proof is a generic symbolic lemma, avoiding concrete-carrier elaboration.
J9164 stopped at dependency preflight before any compiler was launched:
its memo-counting prerequisite object did not yet exist. This invocation has
no wall/RSS/swap/axioms result and is recorded as such. No failed source is
used by an accepted result and no unchanged source/dependency pair was rerun.
