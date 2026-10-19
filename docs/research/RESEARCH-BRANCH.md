# The `research` branch

Created 2026-10-19 in the repo cleanup. The repo now has two long-lived
branches:

- `main`: the v5 and v7 systems, as deployed and closed. Unchanged by this
  cleanup (tip 8a01a9a14).
- `research`: the frontier. Everything that was being pushed on
  `codex/100bit-spend-path-20261013` (R1 soundness and the Rust), on
  `v8-reference` (R1 privacy, formerly the R0 track) and on the integration
  side branches, in one history.

Every other branch is archived as an annotated tag `archive/branch/<name>`
at its final tip, and then deleted. Nothing is lost: `git checkout
archive/branch/<name>` restores any of them.

## How `research` was assembled

In order, each a merge with no conflicts and no change outside
`docs/research/`:

1. `codex/100bit-spend-path-20261013` at f59a21fc1 (Decision 1h accepted:
   the R1 source runs on SBF again).
2. `v8-reference` at f9bb4992a (privacy LOG D54–D65).
3. `codex/r1-privacy-build-integration-20261019` at 2ef9bf896 (the unified
   Lean base, manifests 1–2).
4. `codex/100bit-proof-paused-20261019-1c42e3f41` (the live session's paused
   proof-candidate snapshot).
5. Removal of `docs/research/v8-r0-zk-20261009/lean/R1Mirror/`, which nothing
   imported any more.

`research` does not contain `main`'s last 507 commits (the v7 closure replays
and the 2026-10-09 rationalisation). The two diverged at e97c66639, and a
merge would conflict in `crates/aspis-core` and `programs/aspis-pool`. The v5
and v7 systems are `main`'s, and R1 is `research`'s; neither needs the other.

## One R1

Soundness and privacy must be theorems about the same R1. Where that stands:

- **One source of definitions.** The privacy closure (402 modules) builds in
  one ordered build on one base, against the spend path's own opening-layer
  modules (LOG D63, D65). The hash-recorded copies in `R1Mirror/` were
  deleted in step 5. `line_identity` is stated over the spend path's own
  constants.
- **One payload.** The privacy model of the R1 payload (Z9, LOG D27) was
  taken from spend-path revision 1822c2ced. Since then the production source
  changed only in `r1_semantic.rs`, `transcript.rs` and `verifier.rs`, by the
  extraction refactors and stack fixes of Decisions 1–1h, each gated on
  byte-identical codec and ordered-trace output. The prover-side source
  (`prover.rs`, `host_semantic.rs`, `sampler.rs`, `r1_wire.rs`,
  `aspis-prover`, `aspis-statement`, `aspis-core`, `aspis-pool`) is unchanged
  since the builder differential pin 0c46bf447. This is a tested fact about
  the gates, not a theorem.
- **One sampler.** `QM31SamplerLaw` is proved from the spend path's extracted
  `qm31_sample` (D63.3), to be composed end to end in manifest 2.
- **Still two descriptions, joined by named premises.** The privacy games
  take the Rust prover through the refinement premises of LOG D52.2 (R-rom,
  R-causal, R-commit, R-wire) and the builder through `BuilderRefines`
  (D46, D51), discharged for the extracted copies (D54–D61) and linked to
  production by differential tests. The prover-side check is proved sound
  for the extracted checker (D57–D64), with the remaining column builders
  as hypotheses. Each premise names the Rust fact it stands for. Closing
  them is the refinement work on this branch.
- **What must still be unified.** The soundness roots are not yet in the
  unified build: three imported modules have no committed source
  (`R1FunctionalBatchClean`, `R1SubfieldBatchStage2`,
  `AspisR1Qm31ArithmeticProbe.Funs`, the last now promoted on the
  integration branch), three files are imported under two module names
  (`SpendRelation`, `SpendAppendBinding`, `TraceAppend` as `X` and `R1X`),
  and three names collide. The privacy relation is Rspend⁺ := Rspend ∧
  (transfer → change[7] ≠ 0) (D50); soundness extracts Rspend.

## Working on `research`

- All sessions push here. Worker side branches are fine while a job runs;
  they are merged here by the lead and then archived.
- Decisions and acceptances continue in the two logs:
  `docs/research/v8-r0-zk-20261009/LOG.md` (privacy) and
  `docs/research/100bit-spend-path-20261013/design/` (soundness and
  Rust).
- Release evidence is only what checks in one clean ordered build on the
  unified base (D63). Focused compiles are working evidence.
