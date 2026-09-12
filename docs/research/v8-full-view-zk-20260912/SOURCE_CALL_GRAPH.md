# Rank-gate and entropy call graph

Audited at `9e432896a4e1515efebe940b71fd9b4f9f009189`.

## Existing gated Spend path

- `crates/aspis-prover/src/state_only_good_spend.rs:249-367` evaluates the
  q18 root-neutral, raw-tail and product rank predicates.
- `crates/aspis-prover/src/state_only_spend.rs:869-920` derives three
  schedules, invokes the selector callback, and only then serializes the
  selected branch.
- This path has q18/profile-specific constants and is not silently reusable as
  a q22 certificate.

## Selected reconstructed generated positive-V8 host path

- `relation_callback.rs:36-37` includes `positive_transfer` under
  `v8_positive_transfer`.
- `relation_callback.rs:314-340` selects the payment/performance modules and
  calls `payment_extraction::performance::run()` under `v8_performance`.
- `performance.rs:100-147` compiles the positive case, constructs fixed
  attempt secrets, applies the active row-1014/column-3 overwrite and begins
  proof construction.
- Later in that same function, q22 is derived, openings/frontiers are built,
  the body is verified, and the proof is written.
- Neither the generated files nor this path reference
  `state_only_hiding_rank`, `check_state_only_complete_hiding_rank`, or any
  `probe_*rank` function.

Therefore the repository's existing q18 gate is active for its native Spend
builder but is not invoked by the selected reconstructed repaired q22 host
demonstration before serialization/publication. This does not authenticate
every deployment path while P0 and the production entropy adapter remain open.

## Entropy boundary

- `state_only_entropy.rs:154-169` defines
  `deterministic_spend_fixture` under test/insecure-fixture cfg.
- `state_only_entropy.rs:172-190` defines `StateOnlyAttemptSecrets::generate`
  from 96 OS-random bytes split into three components.
- `state_only_entropy.rs:196-224` defines the deployed-proof API
  `generate_for_mask_nonce`: the proof-account public key supplies the public
  nonce and 64 fresh OS-random bytes supply the two private seeds. This is the
  selected API for the intended adapter.
- Reservation/build entry points begin at lines 235, 286, 339 and 392 and
  reserve before private material derivation.
- The selected generated performance path calls the deterministic fixture and
  `InMemoryStateOnlyMaskNonceStore`; it does not call `generate()`.
