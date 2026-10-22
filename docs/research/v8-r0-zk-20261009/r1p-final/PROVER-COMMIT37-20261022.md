# Prover commitment continuation 37

**Target not yet established.** Intended trust list: P1 (shared SHA-256 ROM),
P7, TrustedStd, E1 (successful OS RNG draws), E2 (atomic create-if-absent and
persistence). Intended scope: D146 deployed statement image, D143 public
statement/proof bytes and oracle answers; timing and other side channels are
outside the privacy contract. No endpoint premise removal is claimed.

Actual task base: `fc5a92af71efc9c1d3a2a59012ab2bd4438bebc2` (the handoff cited research `26b922be6`). Branch: `codex/cx-prover-commit37-20261022`.
No shipped source changed.

## Stage 1: ROM coordinate and event audit

`ProverCommitReservationRom37.entry_mass` proves the entry-count bound for a
fresh uniform SHA-256 ROM answer. `fresh_coordinate` fixes every other ROM
coordinate and permits arbitrary ledger entries depending on that fixed
context. `prior_preserved` proves that the coordinate extension preserves
all earlier distinct queries. These are P1 model facts, without a hash
regularity hypothesis. They do not yet instantiate the source's selected
nonce, nonzero rejection, sixteen-draw generation or eight-attempt owner.

`reservation_length` checks the exact 39-byte reservation domain plus the
32-byte nonce. `not_simulator_seedPoint`, `queried_not_seedGuess` and
`no_existing_event_containment` prove that the existing seed event does not
contain queries on reservation inputs. This is an event-interface finding,
not a claim of a SHA-256 collision or a privacy attack.

J9135 is a rejected simplification draft; J9136 compiles the corrected seven
theorems, exit 0, wall 1.93 s, peak RSS 4,057,200 KiB, zero swaps. All seven
accepted axioms audits contain only subsets of [propext, Classical.choice,
Quot.sound]. Exact sources, dependency hashes and raw receipts are retained
under `evidence/prover-commit37-20261022/`. Each job has its own capped scope
(MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64; Lean -M7000).
No cold dependency build or full regression ran.

## Stage 2: conditional ROM memo counterexample

`ProverCommitReservationMemo37.generic_memo_mass` computes the exact
conditional ROM mass after one prior query. Fix a nonce `known` and its
oracle answer `entry`; the adversary chooses one ledger entry equal to that
answer. All remaining coordinates stay independently uniform. For an
independent uniform raw nonce the hit mass is `2/N - 1/N²`, N = 2^256,
strictly greater than the fresh-entry bound `1/N`.
`conditional_memo_mass` and `memo_exceeds_fresh_bound` specialize this
symbolically to the actual 256-bit carrier. This is an actual conditioned
ROM model, unlike part 36's generic constant-hash countermodel.
`old_event_absent` proves the old simulator-domain event has mass zero for
that prior query list for every simulator seed. The missing memo-hit charge
therefore matters quantitatively as well as pointwise.

J9137–J9145 are rejected elaboration drafts (decision/Fintype instance
normalization; no resource-cap violation and no recursion limit raised).
J9146 compiles the four final theorems, exit 0, wall 1.97 s, peak RSS
4,061,132 KiB, zero swaps; only standard axioms. This raw-draw computation
is explicitly before nonzero conditioning; no complete native retry bound
is claimed from it.

## Stage 3: nonzero, retries and source frames

`ProverCommitReservationNonzero37.mixed_memo_mass` allows different nonce
and digest carriers. `nonzero_memo_exceeds` proves the same strict violation
of the fresh-entry bound even granting an exact-uniform nonzero nonce:
with d = 1/2^256 and p = 1/|NZ|, the conditional ROM mass is
`d + p*(1-d) > d`. The known nonce is nonzero. The remaining ROM coordinates
are independent uniform answers, not a fixed or constant hash.

`rejected_prefix_success` and `retry_query_not_covered` follow the existing
sixteen-draw generator: every legal 0..15 all-zero rejected prefix can be
followed by a successful nonzero 96-byte candidate, and a query for that
nonce's reservation input still cannot satisfy the old seed event. These
are exact control/event results. They do not assert that the bounded native
sampler is an always-successful nonzero sampler, erase entropy failures,
or prove the complete native selected-nonce probability law. OS errors and
sixteen-zero exhaustion retain the earlier source semantics and E1 contract.

J9147 is a rejected control-lemma draft; J9148 compiles the four corrected
theorems, exit 0, 2.01 s, peak RSS 4,062,824 KiB, zero swaps. All accepted
theorems have only standard axioms. The rejected tactic draft also exposed
that overriding decision instances interferes with tactic-generated proof
terms; those local instances are removed before the arithmetic/control
proofs. No kernel limit or heartbeat setting was raised.

`ProverCommitReservationFrames37` proves the reservation byte-input map
injective (so its nonce-indexed ROM restriction has genuinely distinct
coordinates), and general first-byte/byte-32 separation criteria.
`reservation_control` fixes byte 32 of the reservation frame to ASCII t
(116). Native source inspection, pinned in `source-frames.json`, finds:

- Public statement digest input begins with the variant byte 0 or 1.
- P3 binding and simulator coin frames begin with U (85).
- The selected Merkle leaves/parents begin with 0x10/0x18 (the legacy
  binary parents begin with 0x11).
- State-prefixed transcript absorb/squeeze/advance/grind inputs have byte
  32 in {0,1,2,3}, which differs from 116 even when their first 32 bytes are
  arbitrary ROM output.
- Native entropy derivation/expander domains and the transcript-init domain
  have fixed prefixes that differ from the reservation domain before any
  variable suffix begins.

Thus no reservation/protocol input overlap was found in these source frame
families. Adversarial queries are unrestricted and can of course query a
reservation input. The source inspection is not promoted to a verified
complete call-graph refinement. In particular, the direct `Sha256` call in
`reservation_path` still needs source-to-shared-ROM transport under P1;
this job does not silently replace that call with a fresh independent draw.
No native source finding requiring a shipped change is claimed.

J9149 compiles the first three grammar lemmas (exit 0, 1.70 s, RSS
4,040,924 KiB, zero swaps); the additive injectivity lemma is compiled at
J9150 (exit 0, 1.74 s, RSS 4,040,968 KiB, zero swaps). Only standard axioms;
the two fixed-byte facts need no axioms.

## Demonstrated obstruction and exact next interface

D149 correctly supplies the cryptographic model P1. The instruction that
reservation memo hits are already covered by
`ProverCommitSeedEvent19.seedGuess` is false for that existing definition.
It tests the prefix `UNPROVED:R1:SIM:COIN || simulatorSeed`; a reservation
query starts `aspis:state-only:attempt-reservation:v1 || mask_nonce`.
`no_existing_event_containment` formally disproves the required inclusion,
and the conditional ROM example shows that omitting the memo case makes
the single-entry fresh-address bound false. Nonzero rejection does not
repair the inclusion. This is a correction to the proof interface, not a
privacy attack or a claim that the desired complete numerical bound is false.

**Exact next deliverable:** a source-to-shared-ROM transport for
`DurableStateOnlyMaskNonceStore::reservation_path` composed with
`ProverCommitLedger36.prepare`, carrying the actual prior oracle history,
byte-blind initial ledger/additions and schedule, and the selected nonzero
nonce from the sixteen-draw/eight-attempt owners. It must handle
`reservationQueried queries nonce` explicitly. Either prove a memo-preserving
real/simulator coupling for that case, or define and bound a joint bad event
that contains both reservation memo queries and the existing simulator-seed
queries, then prove that its *whole-run* charge fits the stated endpoint.
Do not assert containment in the unchanged old event.

The existing seed-event bound can be reused as a counting technique, but
its theorem cannot establish containment for a different byte domain or
secret. No reservation-event allowance is silently installed into the
headline, and no new cryptographic assumption or TrustedStd field is added.
A union bound for all accepted retries must retain all previous queries,
ledger additions, repeated nonces and rejection conditioning; counting only
eight successful entropy draws is insufficient for sixteen-draw generation.

Per the requested stop rule, work stops on this demonstrated event-interface
obstruction. Native simulator publication (proof bytes, ordered tables,
merge, early errors), the D143 source-to-FSExperiments conversion,
`shippedProverExperiment`, both WholeRunJoins for every byte-blind schedule,
and the endpoint without RustProverRefinement remain open. No claim of a
native selected-nonce push-forward discharge is made. The security target
is unchanged and **not yet established**.

## Actual endpoint before/after: unchanged

No statement-domain or environment quantifier is installed in the active
endpoint. Its `x : Statement K CommitHandle` and independently supplied
`rust : FSExperiments ...` remain quantified as before, with
`RustProverRefinement` explicit. The desired D146 statement-image restriction
and adversary-owned initial ledger/schedule belong to the unfinished endpoint,
not this theorem. Intended E1/E2 appear visibly in this report's trust list;
they are not claimed as discharged or integrated into the active headline.
P1 is reused, not added as a new hash assumption. No existing premise,
failure event, numerical bound, budget or conclusion has changed.

Full before/after source snapshots for the active fuel endpoint, the older
headline and TrustedStd are retained under `endpoint/`; their diff is empty.
The following is the verbatim active theorem declaration, using its existing
local notation. Its full surrounding binders are in the snapshots.

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
