# Design history

The default branch is the public Aspis Spend release surface. It keeps the
current implementation, the source modules required by the q18/g37 release,
the paper source, and the tooling that certifies and executes a release.

The pre-publication research tree is preserved by two immutable tags:

- [`research-archive-2026-07-14`](https://github.com/DJBarker87/aspisZK/tree/research-archive-2026-07-14)
  (commit `020f8f87238435dc2e1dc8cb41df90670fcb94f6`): the earlier root
  workspace, rejected parameter iterations, superseded certificates, negative
  experiments, and the full sequence of failed or abandoned designs.
- [`research-archive-2026-07-15`](https://github.com/DJBarker87/aspisZK/tree/research-archive-2026-07-15):
  the working tree immediately before the production-surface strip,
  including the local-validator measurement harness and the superseded
  design-iteration modules later removed from the default branch.

The archive is a set of Git tags rather than copied directories. This keeps
the default checkout focused; Git history remains the authoritative record
for individual changes and their chronology. During research the release now
named Aspis Spend was tracked under an internal iteration number, which
appears throughout the archived trees and their file names.

## Origin

The project began on 2026-04-19 as an SVM cost model for transparent-proof
verifiers (commit `d0d7605`). The calibration target was the verifier from
Jotaro Yano's measurement study
([IACR ePrint 2025/1741](https://eprint.iacr.org/2025/1741),
[solana-pqzk-fullchain](https://github.com/pqzk-labs/solana-pqzk-fullchain)),
which had shown a minimal Winterfell STARK verifying inside one Solana
transaction on devnet. The first commit carries that verifier's measured cost
profile (`examples/phase1/pqzk-real-verifier-profile.yaml`: 435 SHA-256
syscalls, 27,804 hashed bytes, 54 Merkle paths, a 4,211-byte proof) next to
hypothetical circle, FRI, and WHIR profiles scored by the same model.
Reproducing and measuring his result was the first milestone. Everything
afterwards asked whether that budget could hold a shielded spend, a real
relation with an atomic nullifier and pool transition, rather than a minimal
counter. The construction that eventually fit shares no components with the
prototype, but the feasibility direction is owed to that paper.

## R1 replaces V7 (9 November 2026)

On 9 November 2026 the owner decided that R1 replaces V7 as the current
implementation on the default branch. V7 verified a spend and settled it in a
single transaction and was measured only in local runtime tests; R1 splits
verification across two transactions joined by a checkpoint account, uses a
57,607-byte compact proof, and was developed on the `research` branch with
the aim of 100-bit classical soundness per attempt and no proof-of-work
credit. `crates/` and `programs/` now hold the frozen R1 source (revision
`4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`, with the Pool at
`b936275465600469312d1f058cdc91ea2a11f3dc`), taken from research commit
`07123926e88273271344977a3fdc26d1780cde14`, and the R1 proof package is in
[`r1/`](r1/). The V7 records stay under [`v7/`](v7/) and in the dated
research notes, and the V5 mainnet record is unchanged. The R1 release target
is not yet established; the remaining gates are listed in
[`r1/OPEN-GATES.md`](r1/OPEN-GATES.md).
