# R16 source integration ledger

Date: 2026-09-20. Privacy worktree base: `4b82e266`.
Pinned recovered host base: `9e432896a4e1515efebe940b71fd9b4f9f009189`.

## Candidate and scope

`tools/stage_r16_basis_host.py` creates a new, isolated research host from
the authenticated R15 reconstruction. It records every edited file's before
and after SHA-256 and the shared transport module's SHA-256 in
`r16-stage.json`. All seven recoverable generated inputs are authenticated
before modification. The three unavailable non-host preimages remain
unavailable; this is not a recovered deployment build.

The shared transport is used by both M31 C1 and QM31 C2 encoding, OOD
evaluation, original-functional inverse-dual weights and terminal weights.
Semantic computations and their point claims remain in the original row
basis. The inverse dual precedes chord transpose. Linear gamma batching
commutes with the common transport. The immutable source-derived map is
included in the functional descriptor; prover and verifier both absorb
`AV8/R16/basis89-dual-dense/research-v1` before the old transcript prefix.

The old optimized terminal routine is replaced by a dense implementation:
evaluate each inverse-dual entry, apply chord transpose, then fold. The
separate dense reference starts from the materialized original weights,
applies the inverse dual, chord transpose and folds, and still checks all
four terminal entries. The complete structured/dense verifier outcome
comparison and original proof-corruption controls are retained.

Only the selected performance-host entry point is integrated. Unselected
historical entry points compiled in the recovered files are not claimed to
implement R16. Production source paths, original source pins and the C1
negative regression are unchanged. There is no deployment, oracle override,
nonce search, live account context, or new hiding assumption.

## Focused algebra tests

`cargo test --offline --locked --release --jobs 1 -p aspis-prover --lib
r16_basis_repair -- --nocapture`: four passed, exit 0; wall 17.66 seconds,
peak RSS 509706240 bytes, swaps 0 (compilation 17.14 seconds, tests 0.13).
This rerun was required by the shared-module refactor and added QM31 test.
It checks all four extension-field unit limbs at all 1024 positions for
inverse and dual identities, a dense batching identity, the retained raw
rank fixture, and the complete finite-domain low-factor correspondence.
It is not a quantified Lean proof of Rust field operations.

## Integration failures retained, not suppressed

1. Initial staged build: exit 0, wall 51.30 seconds, RSS 596967424 bytes,
   swaps 0. World-0 run: exit 101, wall 7.17 seconds, RSS 218054656 bytes,
   swaps 0. Semantic verification returned code 4: the new profile marker
   had been added to the prover but not the independent verifier. The
   replacement changes verifier transcript initialization, not acceptance.
2. Corrected-marker build: exit 0, wall 46.49 seconds, RSS 602587136 bytes,
   swaps 0. World-0 run: exit 101, wall 7.35 seconds, RSS 218038272 bytes,
   swaps 0. Semantic verification passed, but the terminal differential
   compared new-basis weights to an old-basis reference. The replacement
   applies the specified inverse dual to that reference; it does not delete
   the comparison or modify its expected equality.

The failed source directories and logs remain under
`/tmp/aspis-r15-host.drHYn9/`, named `r16-basis-source`,
`r16-basis-source-v2`, `r16-world0.log`, and `r16-v2-world0.log`.
Neither failed run published a proof file. All builds use offline locked
release mode, one Cargo job, and the exact selected flags/features recorded
by the staging manifest. Work is small host compilation and fixture
generation, not a large certificate aggregation. No Lean file changed in
this integration milestone; a new axioms audit is not applicable.

## Corrected integration results

The final staged source is `r16-basis-source-v3`. Build exit 0, wall 46.59
seconds, peak RSS 638156800 bytes, swaps 0. Its `r16-stage.json` SHA-256 is
`e9097920f786e64a424a32f91987e18b3065929e15c0a2e4923ce699e7f50d05`.

Both same-public synthetic witnesses produced complete accepted 39554-byte
proofs, using ordinary SHA, fixture seed 1 and zero nonce-search attempts:

| Run | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | ---: | ---: | ---: | ---: |
| `r16-v3-world0` | 0 | 7.38 | 218316800 | 0 |
| `r16-v3-world1` | 0 | 6.76 | 218284032 | 0 |

Each execution passed all ten semantic rounds, quotient/image checks,
verification from public bytes, structured/dense verifier agreement and
the three byte-corruption plus truncation controls before proof publication.
Startup controls checked 16384 inverse-dual entries and 64 terminal entries.
The two `public.bin`, `transition.bin`, and `binding.bin` files were compared
byte-for-byte and are identical. The proof files differ, as expected:

- World 0 proof SHA-256:
  `a1a8d949985d61cac9b47b9425df9266d8d7381f075aa95f9591a5c3b9f12b9a`.
- World 1 proof SHA-256:
  `ec25c75a8ba48163a96038929e571fe91d6d248b3af0aff0d185ea537c649e50`.
- Common public SHA-256:
  `9e10f3c9eef4aba72ee047fdf48abdc3ab726a7085ae6381d5a8782bc34e19ad`.

Reproduction: stage a NEW directory with the tool, build its manifest using
the exact `rustflags` and `features` from `r16-stage.json`, with
`cargo build --offline --locked --release --jobs 1`. Run its binary with a
NEW output directory, `ASPIS_V8_POSITIVE_CASE=honest`,
`ASPIS_R16_SELECTED_SECOND=0` or `1`, and `NO_DNA=1`. Unset
`ASPIS_V8_MAX_FRONTIER_SCAN`, `ASPIS_V8_LIVE_CONTEXT`,
`ASPIS_V8_COMPLETE_CONTEXT`, `ASPIS_R15_ORACLE_TABLE`, and
`ASPIS_R15_FINAL_NONCE`. Source staging never overwrites an existing directory.
Logs are retained beside the output directories with `.log` suffixes.

These are fixed-entropy synthetic account fixtures, not an entropy-backed
deployment adapter or a distributional indistinguishability experiment.
Acceptance does not show the retained mask coins hide the whole transcript.

## Outstanding security obligations

Passing complete-host fixtures establishes only exercised correctness,
not soundness or privacy. The first proof boundary remains composition of
the arbitrary-fibre interpolation theorem, maintained natural-basis
conversion, and exact balanced-mask transport. Beyond that, establish a
single joint posterior/coupling for the changed source view, preserving
all already-used coins through C2, semantic messages, point/OOD/final
values and openings. Raw rank must not be reused as an independent fresh
pad after those observations. Shared-oracle/seed refinement, visible
failures, retries/publication and an explicit global loss remain open.
