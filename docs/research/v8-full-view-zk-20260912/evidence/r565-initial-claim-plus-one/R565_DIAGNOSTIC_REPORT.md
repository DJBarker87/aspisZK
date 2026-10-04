# R565 initial-claim-plus-one recipient-zero diagnostic

## Result

One fixed `recipient_zero`, seed-1 diagnostic ran in a fresh isolated copy of
the frozen R117 source. It changed the carried initial semantic claim by
exactly `K::ONE` after C1/C2 messages and roots were built, checked against the
immutable R555 seed-1 artifact, and before the claim was written into the wire
and passed to `semantic_start`.

The run exited 0. It reported all of the following:

- public, binding, and transition bytes equal the immutable R555 artifact;
- C1 and C2 roots equal the roots parsed from the immutable R555 proof;
- all 28 independently recomputed first-round terminal coefficients satisfy
  the checked affine relation at `eta=0`, `eta=1`, and the actual `eta`;
- the retained genuine-polynomial fixture reports `first_boundary_wrong=true`;
- exactly one programmed post-round-zero squeeze yielded `z0=0`;
- both selected verifier entry points returned `Ok(())` and the retained
  corruption, truncation, and noncanonical controls passed.

This is a single programmed-oracle diagnostic. It is not a SHA-256 attack,
probability statement, security-game conclusion, privacy proof, soundness
proof, or end-to-end security result.

## Exact scope and pins

- Frozen source revision: `6677d5f1310ff7373301fbd79f186278f772e68a`.
- Fresh isolated root:
  `/home/dombarker/project-offloads/aspis-r117-initial-claim-plus-one-20261004-a`.
- Full selected flags plus only host cfgs `v8_semantic_rejoin` and
  `v8_initial_claim_plus_one`; release overflow checks were enabled.
- Selected verifier and positivity source remain byte-identical to R555/frozen
  pins: `performance_verifier.rs` SHA-256
  `d6dad89eaa8d735f467055e96a8df12de7a391e2475ec26c44b2bc493624a62a`,
  `positive_transfer.rs` SHA-256
  `3a19043d2f40f168cb2127ba46e1795db7ea0751625c4fe48c73e02dab533cab`.
- Final host source hashes are in `FINAL_SOURCE_SHA256SUMS.txt`; raw selected
  flags are in `selected-rustflags.base.txt`.

## Build and run records

- Build 1: exit 101, 27.11 s, 594,052 KiB RSS, swap 0. It failed only with
  Rust E0716 at `parse(&std::fs::read(...))`; full log and pre-fix source are
  retained.
- The only follow-up source repair named the proof byte vector
  `prior_proof_bytes` before parsing it. The exact one-line diff is
  `performance.lifetime-fix.diff`.
- Build 2: exit 0, 11.40 s, 557,056 KiB RSS, swap 0.
- Run 1: exit 0, 8.39 s, 620,304 KiB RSS, swap 0. The complete raw log,
  command/flags, input and output checksums, generated body, public,
  transition, binding, and programmed entry are retained in `remote-evidence/`.

The first-round affinity computations use only `terminal_with_g` and
`interpolate_degree27` with temporary `s.eta` values restored before the
existing boundary and transcript code. They make no transcript/oracle calls.
No search, retry, nonce scan, or second seed was run.

## Boundary

The diagnostic exercises one deliberately programmed challenge and one
synthetic fixture. It does not show that this path arises under the ordinary
shared oracle, that a public statement has an admissible alternate witness,
or that a privacy or soundness game is won. No release conclusion follows.
