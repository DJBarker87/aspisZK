# Lead decision: per-deployment program ids in the R1 verifier (2026-10-20)

Finding (devnet job cx-devnet, `evidence/devnet-r1-20261020/REPORT.md`): the
frozen verifier checks the Pool program against
`AUDIT_POOL_PROGRAM = [0x41; 32]` (`programs/r1-cost-probe/src/r1_pool_adapter.rs:77`,
used at :517 and :880), a placeholder with no keypair. The registry id is
pinned the same way. Every R1 measurement ran under LiteSVM, where the
harness installs the Pool at that id. The frozen ELF `8cf8d84e…` therefore
cannot settle on any real cluster.

Decision: the Pool and registry program ids are per-deployment build
constants (an env/feature-supplied 32-byte value each, defaulting to the
audit placeholders so every existing gate and pin is unchanged). A
deployment pin records the ids, the resulting ELF SHA-256, and a check that
its `.text` and `.rodata` other than the two constants are byte-identical to
the frozen build. The comparisons are by bytes, so this is a data change;
the source freeze (`LEAD-REVIEW-FORMAT-ADOPT-20261020.md`) is amended to
"frozen up to the two deployment constants", and the CU bound and re-pins
carry over by the same `.text`-identity argument used for panic-line shifts
(`LEAD-REVIEW-CU-BOUND-2-20261019.md`). Reading the ids from the registry at
runtime instead is a logic change and is not taken now.
