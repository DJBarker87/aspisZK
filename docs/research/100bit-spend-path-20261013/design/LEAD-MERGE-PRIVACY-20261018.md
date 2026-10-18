# Lead note: v8-reference (R1 privacy) merged into the 100-bit branch (2026-10-18)

The user approved this merge. `origin/v8-reference` (e171d7418, LOG D45) is
merged into `codex/100bit-spend-path-20261013`. It brings 181 commits, all
under `docs/research/` (almost all in `v8-r0-zk-20261009/`, plus
`v8-r1-20261011/` and one `v8-r0-rust-20261009/` file). The merge was
clean. No production crate, program or spend-path Lean module changes.

## What this brings

The R1 privacy development, LOG D24–D45 in
`docs/research/v8-r0-zk-20261009/LOG.md`:
- `R1Z/PrivacyR1.privacy_R1`, `R1Z/SimulatorR1.privacy_R1_eff` (explicit
  simulator simE) and `R1Z/PrivacyGamesR1.privacy_R1_games` (concrete
  R1 games). These give ZK_FS for the honest retrying R1 prover with error
  ≈ 2^-108, dominated by the LogUp pole term.
- `R1Z/BatchedAlgebra.line_identity`: the second fold on the line domain
  commutes with the encoder, for every message and every α₁. The soundness
  side currently assumes this (`R1QueryResidualBridge`), and it may now cite
  it once the build integration below is done.

## What this does not do

- The privacy Lean still builds in the host workspace `aspis-fs-generic`,
  not the spend-path one. `R1Mirror/` holds hash-recorded copies of
  spend-path opening-layer files and must be replaced by direct imports of
  the originals. This is the build-integration job, to be issued after
  Decision 1g restores a runnable SBF source.
- Privacy remains conditional on the hypotheses listed in LOG D45.4/D45.5:
  - the lazy-programming coupling;
  - game agreement and the commitment-read layout;
  - the exhaustion mass;
  - Sem1Uniform;
  - builder completeness;
  - the R-wire, R-ser, R-commit, R-causal, R-retry and R-pub refinements.
- The prover-side changes the privacy theorem requires are not applied:
  the P_R1 check, the retry loop with fresh secrets per attempt, a fresh
  proof-account keypair per attempt, and the cap N = 8 (LOG D29.3, D31.2,
  D38.3, D38.4). Each will be a gated source change on this branch.

## Ongoing

Privacy work continues on `v8-reference`, and the lead merges it here
periodically.
