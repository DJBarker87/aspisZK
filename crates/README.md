# Rust crates

These crates are the frozen R1 source. Every file under `crates/` is
byte-identical to research commit `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`,
which is the revision the R1 proofs are stated about; this README is the only
addition.

| Crate | Contents |
| --- | --- |
| `aspis-core/` | Fields (M31 and its extensions), transcript, commitments and the shared verifier arithmetic used both on the host and on Solana |
| `aspis-r1-cost-probe/` | The R1 verifier and prover: compact binary-multiproof proof format, the two-stage verifier with its checkpoint, the sampler and the native client |
| `aspis-statement/` | The private-spend statement, the spend relation and the Pool V1 statement codecs |
| `aspis-prover/` | Earlier host prover, fixtures and security calculators, still used by tests and tools |
| `aspis-pool-wallet-v1/` | Pool V1 encrypted-note envelope, recipient scanner and cursor |

The name `aspis-r1-cost-probe` and the "unproved cost probe" wording in its
manifest are historical: the crate began as a compute-unit measurement and
became the R1 verifier. The text is left as it is because the source is frozen.

The Solana programs that use these crates are in `../programs/`. What has been
proved about this source is described in [`../docs/r1/`](../docs/r1/).
