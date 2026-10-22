# S9 concrete scalar multiplication: direct reuse

This is the preferred callback consumer. It directly imports the existing `AspisR1S3PowersLowTotalV1.wide_mul_m31_total`; it does not reprove that primitive theorem. The new statements derive success of the concrete S9 operation for every stored input, then canonical/exact field meaning for the same returned value on canonical input. No operation-success premise is retained.

Correction to the earlier V1 report: the arbitrary-input QM/wide scalar totality lemmas already existed in the S3 low-powers owner. V1 duplicated their proofs. Its proofs are mathematically valid historical evidence, but are not new primitive arithmetic results and are superseded as the integration path by this reuse consumer. Remaining source/library and caller obligations are unchanged.

Focused replay: Lean 4.32, `-j1 -M4400`, exit 0, 19.528 s, process peak 3,211,067,392 bytes, observed swaps 0; standard axioms only. A replay was necessary because a sibling briefly launched a conflicting Lean job during the first V2 compile and overwrote mutex metadata. The sibling child was killed; its result is not accepted. The central controller now owns all local launches and checks both mutex ownership and foreign Lean processes throughout each run, stopping its own child if either check fails. The accepted replay has no foreign-process samples or watchdog abort. This is a focused repair of missing concurrency evidence, not an unchanged full regression.

Exact source/import/object pins, old producer evidence, argv/profile, sampled global/process-tree RSS and lock observations, raw logs and controller source are included. No objects/binaries are included. S9 and implementation-linked 100-bit soundness remain open.
