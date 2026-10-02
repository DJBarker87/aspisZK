# R215: process all operands of the retained copy statement

The isolated candidate adds a five-line `CopyNonOverlapping` branch to global-access decomposition. Its source, destination and count operands each use the existing visitor. The statement remains intact. The lead inspected this exact delta and validated the bundle checksums. No pointer interpreter, verifier or memory semantics changed.

The cached static release build exited 0 in 6.91 s. GNU time reports Docker client RSS 28,336 KiB; aggregate dedicated build-slice memory is recorded separately. Translation of the identical R210 projection ran once and exited 2 in 0.17 s, child peak RSS 57,728 KiB, zero swaps. It passed the prior copy-routing frontiers and stopped in `TypesAnalysis.ml:229`, while analyzing the `Option` source declaration at `core/src/option.rs:597:0–597:18`. No Lean output was emitted; no theorem or axiom audit is claimed. Both jobs used the prescribed 5/7 GiB zero-swap scopes; the container has matching limits.

The exact patch, retained source, source/binary/input hashes, raw logs, complete command descriptors, status and resource evidence are in [the lead audit](evidence/r215-copy-operands/lead-audit.json). The Aeneas source snapshot has no captured original Git revision; the campaign revision is labelled separately. The compiled binary remains on the pinned host and in scratch.

First remaining proposition: justify treatment of the erased mutable reference region in the monomorphized type, then supply actual selected vector-copy and fold semantics and whole callback chronology. This diagnostic supplies no replacement assumption. Privacy and soundness remain unproved. No CU benchmark or unchanged regression reran; 999,790 / 999,532 CU and every security parameter remain preserved.
