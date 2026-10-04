# R565 — initial-claim reuse diagnostic

## Result

A fresh isolated host copy ran one fixed `recipient_zero`, seed-1 diagnostic
with full selected flags, release overflow checks, and the two host-only cfgs
`v8_semantic_rejoin` and `v8_initial_claim_plus_one`. It changes exactly the
carried initial semantic claim by `K::ONE` after both C1/C2 roots are built and
before the wire and `semantic_start` use it.

The run exited 0 in 8.39 seconds, with 620,304 KiB peak RSS and no swap. It
checked that the R555 and R565 public statement, binding, and transition bytes
are identical; it parsed R555's proof and asserted both C1/C2 roots equal the
newly built roots. It retained the programmed first `z0=0`,
`first_boundary_wrong`, authentication/canonical/error controls, and both
selected verifier calls, which returned `Ok(())`. The first-round true
polynomial was recomputed through the existing `terminal_with_g` and
`interpolate_degree27` path at `eta=0`, `eta=1`, and actual eta; all 28
coefficient affine checks passed.

The selected verifier and positive-transfer source remained byte-identical to
the frozen pins. The final binary SHA-256 was
`bf5292055fab14984fd0e3c9b799709b998d76bef028f17c335d154c9e86387c`.
Formal axioms are not applicable because this is a Rust runtime diagnostic.

## Evidence

[Evidence bundle](evidence/r565-initial-claim-plus-one) contains the exact
source snapshots, full flags and launch commands, complete build/run logs,
resources, failed first build, named lifetime-only correction, final binary
and artifact checksums, produced body, public inputs, and the local R555/R565
comparison. Build 1 failed only with Rust E0716 for a temporary borrowed proof
buffer; that source and log are retained. Build 2 succeeded in 11.40 seconds
at 557,056 KiB RSS, no swap.

The source-dependency evidence includes the corrected R563 inventory and its
frozen source snapshots. It records the actual compact verifier chronology:
it absorbs the initial claim before sampling eta, then absorbs each sent
round record, samples the round point, derives the omitted coefficient from
the carried claim, and evaluates it.

## Boundary

This is one deliberately programmed shared-oracle diagnostic, not a proof of
an ordinary-oracle event. It does not establish a real hash attack, an
adaptive retry probability, a source/game-admissible alternate witness, an
extraction relation, privacy, soundness, or end-to-end security. The first
remaining proposition is the actual lazy shared-oracle adaptive-retry law and
its connection to source/game admissibility and the extraction relation.
