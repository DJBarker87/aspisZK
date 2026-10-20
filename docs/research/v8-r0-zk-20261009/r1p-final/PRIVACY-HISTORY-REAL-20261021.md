# Real privacy history — 2026-10-21

Branch `codex/cx-priv-history2-20261021`, base `de2dd2c8b`.

## Stage 1: whole-run repeated-read obstruction

The literal requested exclusion is false. An event covering **every repeated
read over the whole real run** cannot have small birthday mass. The retained
`OProg` allows `.query a (fun _ => .query a (fun _ => .done))`. This is a
legal, answer-insensitive two-read adversary under the fixed `2^64` observer
budget. It is independent of the proof, instance, honest success and oracle.
The address can be `[]`, which is in every finite-ROM domain.

`QueryScanWholeRunRepeatObstruction.real_game_repeats` proves this for the
exact `GamesR1PBin.realGameP`, in both `firstGood` branches. Its returned
`observerOracle` includes the repeated suffix. These are actual reads of
the complete run. `covering_event_mass_one` proves that **any** event covering
these repeats has mass exactly one, on any finite nonempty random carrier.
`no_small_covering_event` rules out every proposed bound κ < 1, including any
κ for which the requested positive total is below `2^-100`.

This refutes the whole-run *event specification*, not privacy and not a
collision theorem about distinct first-read addresses. In particular,
`BinCombinedMerkleCollision.mass` controls `hitsBad` on **first reads**; its
six-target term is not a theorem bounding deliberate address repeats. Reusing
it for the event requested here would be an event-identification error.

Focused env J 9824: exit 0, wall 1.97 s, peak RSS 3,512,380 KiB, swaps 0.
All five audits use subsets of `[propext, Classical.choice, Quot.sound]`.
9823 records two elaboration errors, repaired by symbolic successor
normalization and reducing let bindings before the match split. No large
carrier or recurrence was evaluated. Full fields, source revision/hash,
dependency fingerprint, exact target, errors and audits are preserved in
`history-real-attempts-9800-9999.jsonl`.

## Remaining work and endpoint status

The requested endpoint is blocked by the event specification above. Existing
modules are unchanged. No theorem named `privacy_R1_protocol_history_real`
is asserted, and no probability hypothesis is disguised as execution data.
A sound next specification must distinguish repeats that invalidate a scan
word's first-read sampling law from benign verifier/observer repeats. It must
prove that each *scan* reuse implies one chosen first-read collision/target
hit, then transport the fresh lazy words and charge that single fixed event
once. Post-proof observer repeats alone cannot belong to that excluded event.

## Stage 2: exact real carrier and independent numerical check

`QueryScanWholeRunRepeatReal.finite_real_repeat_mass` specializes the
counterexample to the retained `fsR1P.RealRand`, a uniform finite table times
eight attempt-secret tuples. It is an unconditional mass-one result for any
honest prover, instance, public statement and acceptance predicates. It uses
the exact `RomFiniteBin.wire` budget, symbolically proving `2 ≤ 2^64`, and
proves `[]` belongs to every finite-ROM domain. It therefore applies to the
constructed phase protocol as a specialization, with no change to its parser,
source joins or builder assumptions. Adding output collisions, self-loops or
prior-read events by union cannot decrease this mass-one exclusion.

Env J 9825: exit 0, wall 1.87 s, peak RSS 3,507,464 KiB, swaps 0; all four
audits use standard axioms. An unused-section-variable linter warning does
not affect the statement or proof.

`QueryScanHistoryRealNumerics` proves the **independent numerical** portion:

- `kappa q = 6 * (q : ℚ)^2 / 2^256`; coefficient `c = 6` matches the
  five-reader-plus-output coefficient of `BinCombinedMerkleCollision.kappa`.
- The candidate *numerical* budget envelope is `q ≤ 2^65`. This packet does
  **not** assert a theorem bounding all actual run reads by that envelope.
- Symbolically, `kappa (2^65) = 6 / 2^126` and `kappa q ≤ 1 / 2^109` under
  that envelope. The proof is monotonicity plus exponent splitting.
- For any κ ≤ 2^-109, the proposed total is at most `4 / 2^109 = 2^-107`,
  which is strictly below `2^-100`.

This validates numerical slack; it does not supply the false event-mass law.
No claimed endpoint follows from this conditional numerical fact.

Final env J numerical attempt 9828: exit 0, wall 2.04 s, peak RSS
3,521,588 KiB, swaps 0; all six audits use standard axioms. 9826/9827 retain
elaboration failures. The final proof uses explicit addition monotonicity;
it neither normalizes the 454-bit term nor enumerates a carrier. Earlier
9826 emitted a threshold warning during arithmetic preprocessing; that tactic
was replaced rather than increasing any threshold or resource limit.
