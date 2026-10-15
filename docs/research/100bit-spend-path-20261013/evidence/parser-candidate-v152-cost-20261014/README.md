# Candidate v1.52 SBF P3 reuse gate

This single local LiteSVM gate used the corrected candidate SBF built with Solana `cargo-build-sbf` 3.1.13 / platform-tools v1.52. It reused the same proof and public bytes as the earlier candidate, control, and historical-artifact reuse comparisons; no new proof or mask draw occurred.

Stage one passed at 1,390,128 CU in a 295-byte transaction. The terminal transfer passed at 1,293,571 CU in an 879-byte TxV0 under the 1,400,000 CU limit and reached `r1:final`. The recorded settlement flags show expected history, lane, and nullifier-marker updates and unchanged checkpoint, entry, master, registry, and proof. The selected verifier artifact is SHA-pinned in `input-pins.txt`.

The fixture result records the reused proof SHA-256 `86d4212e…9ed7c`; the gate did not draw fresh mask entropy. The proof’s earlier origin is the OS-entropy candidate run. This is a local cost-path measurement only; it is not a proof of source equivalence or protocol security.

The cgroup receipt, full gate result/log, ASR2/ASE2 fixtures, and the reused proof/public inputs are retained. Newly generated task key files remain on NUC with mode 0600; key contents were not copied or deleted. No network or funded account was used.


The selected ELF was built from the candidate field patch using platform-tools v1.52; see [`parser-candidate-v152-sbf-20261014`](../parser-candidate-v152-sbf-20261014/README.md). Section hashes and differences against the historical ELF are recorded in [`elf-versus-historical.json`](../parser-candidate-v152-sbf-20261014/elf-versus-historical.json).
