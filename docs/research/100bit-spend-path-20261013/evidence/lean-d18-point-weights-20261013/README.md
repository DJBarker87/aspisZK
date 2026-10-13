# D18 point-weight arithmetic identity

`R1D18PointWeights.lean` defines the row and tensor point products and proves their exact equality. The proof reindexes the ten factors through `Fin 5 × Fin 2`, uses the D18 digit identities from `R1D18Transport`, and relates binary extraction to each radix-four digit. It does not claim Rust source correspondence or protocol/security behavior.

The successful focused check was `bash compile-one.sh R1D18PointWeights v` on the pinned NUC workspace, under `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, and `TasksMax=128`. It exited 0 in 1.70 seconds, peaked at 1,785,168 KiB RSS, and used no swap. The successful output records `#print axioms` for the key lemmas; none lists `sorryAx`.

Attempts a through u are retained with their source hashes, receipts, Lean output, and `/usr/bin/time -v` logs. Earlier attempts failed during dependency setup or proof development; their resource usage stayed below 1.8 GiB RSS. Machine-readable receipt linkage and source/worktree provenance are in `provenance.json`. The worktree HEAD changed after task start because the worktree is shared; both observed commits are recorded there.
