# Poseidon round-chain focused compile

The successful focused target was `R1PoseidonChain`, run with
`/home/dombarker/project-offloads/aspis-r1-concrete-decoder-20261013/compile-one.sh`
on the pinned NUC workspace. The checked source is
`docs/research/100bit-spend-path-20261013/lean/PoseidonChain.lean`, SHA-256
`b7dd2851e4217de867c13abde68c18464f5c47a453f09d1d2ba7364e8891a390`.

Attempt f exited 0 in 1.53 seconds, with maximum RSS 3,320,208 KiB and zero
swaps. The scope recorded `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`,
`TasksMax=128`, and Lean threshold 5,000 MiB. See the exact machine receipt,
timing, and output in `R1PoseidonChain-f.receipt.json`,
`R1PoseidonChain-f.time.log`, and `R1PoseidonChain-f.out.log`.

The source's `#print axioms poseidon_chain` output is
`[propext, Quot.sound]`; it contains no `sorryAx`. The failed focused attempts
a–e are retained with receipts, outputs, timings, hashes, and the exact failed
source snapshots (`R1PoseidonChain-{a,b,c,d,e}.source.lean`). They failed on
proof elaboration while the fold combiner and finite-index transports were
being corrected; no failed attempt was retried unchanged.
