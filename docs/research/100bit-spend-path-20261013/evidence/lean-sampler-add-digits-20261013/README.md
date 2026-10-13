# Sampler carry-pass arithmetic

`../../lean/SamplerAddDigits.lean` defines the requested low-endian digit value and recursive `addDigits` pass. It proves output length preservation, value-plus-carry conservation, output digits below `p`, and a final-carry bound of at most one for a nonempty digit list when `p ≥ 2`, every input digit is below `p`, and the incoming addend is below `p`. The helper carry lemma handles subsequent passes with incoming addend at most one. No source-level mutation or machine-integer claim is made.

The focused target compiled on the pinned NUC workspace `/home/dombarker/project-offloads/aspis-r1-concrete-decoder-20261013` with `bash compile-one.sh R1SamplerAddDigits b`. It exited 0 in 0.90 s, maximum RSS 1,613,472 KiB, swap 0, `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, `TasksMax=128`, Lean threshold `-M5000`. Each of the five printed theorem axiom lists was `[propext]` or `[propext, Quot.sound]`; no `sorryAx` was reported.

Source SHA-256: `174cca73fae636a113242c08f938d451a1234ba237dddfeb3da78afb2ad02b62`. The compiled object SHA-256 is `695a37d7b9a9913bbece940ecc0cd80c8b9e87f5af783cd8e144c729a7fd1107`. Attempt a and the successful attempt b receipts, logs, timings, source hashes, and object are retained under `remote-evidence/`.
