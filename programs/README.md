# Solana programs

| Program | Contents | Pin |
| --- | --- | --- |
| `r1-cost-probe/` | The R1 verifier program: stage 1 (TX1) verifies the first half of the proof and writes a checkpoint account; stage 2 (TX2) resumes from the checkpoint, completes verification and calls the Pool | byte-identical to `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387` |
| `aspis-pool/` | Pool V1: lanes, pair-forest history, nullifier records and withdrawals, with the legacy V1 and prepared-settlement instructions removed | byte-identical to `b936275465600469312d1f058cdc91ea2a11f3dc` |
| `aspis-registry/` | Governed verifier registry used by the Pool to find the active verifier | byte-identical to `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387` |
| `aspis-verifier/` | The earlier V5/V7 verifier program, kept in the workspace for its tests and tools | byte-identical to `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387` |

The R1 verifier is still built from the directory named `r1-cost-probe`, and
its source still describes itself as an unproved cost probe; the name dates
from its first use as a compute-unit measurement, and it is not changed
because the source is frozen. The deployed devnet ELF, its build command and
its hash are recorded in [`../docs/r1/BUILD.md`](../docs/r1/BUILD.md).
