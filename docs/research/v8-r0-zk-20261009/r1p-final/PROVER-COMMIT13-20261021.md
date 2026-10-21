# Prover commitment continuation 13 — 2026-10-21

Branch `codex/cx-prover-commit13-20261021`, base `9f6852af9`.
Evidence: `docs/research/100bit-spend-path-20261013/evidence/prover-commit13-20261021/`.

## Stage 1: explicit canonical admitted-domain endpoint

`ProverCommitAdmittedEndpoint` extends the `PrivacyR1HeadlineOwnedClosed`
namespace with an explicit `Admitted` endpoint. Its `input` is fixed to
`BuilderSource.prover`: the M31 public/witness pairs satisfying the embedded
`RspendPlus` relation, the canonical extracted merged trace, and S2 transport.
It does not claim that a shipped Rust runtime record has been identified
with that instance. That source identification remains peer-owned and open.
The original arbitrary-input endpoint is unchanged; the part-12 counterexample
remains valid there.

`Admitted.builder_premises` is proved from D96's canonical builder theorem;
`PhaseWireLog2Bin.honest` changes no public or build projection. The specialized
endpoint initially retains the premise to make the subsequent deletion-only
change reviewable. J8364 is an excluded missing-CharP elaboration draft.
J8365 passes the focused endpoint and all three printed axiom audits using
only the standard three axioms: exit 0, wall 6.97 s, peak RSS 4159700 KiB,
zero swaps. Exact source/dependency hashes and source revision are in the
receipt. No package-wide build or unchanged regression is run.

## Remaining stages

Formatter/panic unreachability, concrete outer transport and all-family shared
oracle coverage remain to be investigated. No shipped Rust, key, peer-owned
source-identification or runtime-join file is changed.
