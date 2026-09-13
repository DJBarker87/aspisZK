# R9 operational commitment bridge

Date: 2026-09-13.

Status: **operational Lean bridge and source-prefix memoization pass; generated
q22 refinement and first semantic cut remain blocked; no full privacy or
release claim**.

## Results

The R9 leaves compile in the existing cached Lean workspace.  The operational
machine now has explicit eager and delayed interpreters, complete observation
records, an exact local `CommandGood`/`operationalBad` boundary, fixed-tape
marginal projection, and a proof that unused tape slots integrate out.  An
eager pending-cache invariant justifies successful paired materialization.
`nonbad_prefix_forward` constructs the existing R8 `ForwardTrace` by iterating
the actual `advance` functions; it does not accept a caller-supplied synthetic
trace or arbitrary final state.

`coordinate_fiber_cap_of_firstHit` converts one source miss tree for each
fixed omitted-coordinate tail, its source-refinement proof, and its miss-spine
budget into the exact coordinate-fiber premise of R8 `ideal_bad_count_le`.
It does not assume the final bad mass or salt-obliviousness.  The companion
`unorderedPair_card` identifies the duplicate-salt index count as
`Nat.choose (Fintype.card Slot) 2`.

The memoized expansion uses the full salt-derivation address shape: attempt
binding, mask nonce, derivation tag, leaf index, and leaf-salt seed.  Repeated
addresses reuse one full answer.  The reconstructed selected `performance.rs`
prefix has the sharper pattern: it derives each pool salt once in the C1 loop,
retains `salts[i]`, and passes that same value to the typed C2 leaf.  The focused
Rust test exercises the pinned pool helper through exact 437-byte C1 and
220-byte C2 preimages and checks the 26-byte digest projection while retaining
the full 32-byte callback answers.

The observed focused prefix is not a universal adversarial query cap.  Its
2,680 callback calls include mask construction; it contains two distinct salt
derivation calls, one call at index 7, and two leaf uses of the retained index-7
salt.  No private preimages are printed or persisted.

## Preserved boundaries

The C1 q4/q6 negative regression, fixed-block H1 hiding result, conditional
R7 theorem, witness-retaining R8 hop, public-only simulator obligation, and
retry/publication proof remain separate.  No H1-only schedule search was
repeated.  No new hiding assumption or production protocol change was made.

## First remaining source-specific obligation

Construct and authenticate the complete selected generated q22 closure, then
prove that its entire pre-disclosure SHA chronology refines
`NonBadOperationalPrefix` and the per-tail `ProbeTree`.  Portable reconstruction
still fails closed on these required preimages:

* `programs/aspis-verifier/src/v7_pair_forest_dispatch.rs`, required SHA-256
  `6638cd3974e5973757333dc5f096dc563f6e0b80aeeee8e60b294e2c15436c80`;
* `programs/aspis-verifier/src/lib.rs`, required SHA-256
  `d96ef7f264efbffe696a697c79ecc707b983f321910d0d857d745b1426057245`;
* `results/v7-pair-forest-combined-rejection-litesvm-20260828/harness/src/main.rs`,
  required SHA-256
  `251aba0b81db74a2c6916c1a522d8a4e3fa63c422fa4797ada53d4132c0398f1`.

Until that closure is authenticated, the actual q22 source prefix and its
universal first-hit premise are open.  Consequently R9 does not advance to the
first semantic polynomial.  Once the source premise closes, the next cut must
stack the sent degree-27 coefficient vector with prior observations using the
same H1 pad; it may not infer full privacy from the resulting conditional
affine lemma.
