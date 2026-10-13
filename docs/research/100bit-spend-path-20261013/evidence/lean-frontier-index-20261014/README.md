# Frontier index counting lemma evidence

The focused NUC target `R1FrontierIndex` compiles the exact indexed-slot count identity and its `index < 2^n` corollary. The source base is `fd4aff50d1c5d977b6dda12e01356e3a1f0d258a`; final attempt `e` is green. Failed proof iterations `a` through `d` are retained with their exact hash-matched source snapshots and runner outputs.

The green source is `docs/research/100bit-spend-path-20261013/lean/FrontierIndex.lean` with SHA256 recorded in `manifest.json`. Its two `#print axioms` results contain only `propext`, `Classical.choice`, and `Quot.sound`. The NUC runner used MemoryHigh=4G, MemoryMax=6G, MemorySwapMax=0, TasksMax=128 and threshold 5000 MB. No dependent or full regression targets were run. The compiled object remains in the pinned NUC workspace at the path in `manifest.json`. `SHA256SUMS` covers this evidence directory except itself.
