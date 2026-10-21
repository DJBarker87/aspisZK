# Default/devnet ID-slot identity check

This supplemental check rebuilds the same isolated three-source candidate with the devnet deployment-ID template. It is an artifact identity check only; nothing was deployed. The build used the retained NUC workspace/cache and an admitted cgroup (`MemoryHigh=2 GiB`, `MemoryMax=4 GiB`, `MemorySwapMax=0`). The incremental build completed in 2.368 s with 202,028 KiB process peak RSS and zero swap.

The default and devnet artifacts have equal size (1,508,152 bytes), identical section tables, and byte-identical `.text` (1,470,760 bytes; SHA-256 `dcd7b1e9452ef7772750c59263cf7d28ec654a22e9ba82112956d2a1cb15e4f5`). Exactly two 32-byte `.rodata` slots differ: pool ID at file offset 1,471,048 and registry ID at 1,471,080. The complete identity report records 63 differing file bytes, because the two IDs differ in 63 byte positions.

The source-inventory check rehashed all 58 files in the frozen source manifest on the candidate workspace. Only `fast_dots.rs`, `fast_pairing.rs`, and `weights.rs` differed, at the candidate hashes recorded in `../source-pins.json`.

`identity.py` is retained as the comparison tool. Its JSON repeats an inherited hard-coded source revision `731018bdc`; that value is stale for this candidate and is explicitly not used as the candidate revision. The actual source revision and per-file hashes are in `identity-candidate-binding.json` and `source-inventory-check.json`.
