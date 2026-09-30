# V7 production packed decoder canonicality

Source parent: `67073b0d1` (production decoder scanner canonicality).
Checked source SHA-256: `44ab712bbf2e1c2727d70ff11405f42e4a1db5de04dd62d2d3613138c1475f0b`.

Focused target: `V7ProductionCallbacksR30PackedDecoderCanonical.lean`.
Host: `dombarker@100.108.41.90`, pinned Lean **4.32.0** and existing R26/R29/R30 cache.
Command: `systemd-run --user --scope -p MemoryHigh=7G -p MemoryMax=8G
-p MemorySwapMax=0 bash .../check-r30-decoder-focused.sh
67073b0d1+outer-working V7ProductionCallbacksR30PackedDecoderCanonical`.
The wrapper invokes `lake env lean -j1 -R` for this single file.
Scope: `run-rf3c0eb56815b42feba6e0415a86f059b.scope`.
Result: exit **0**, wall **4.81 s**, peak RSS **2,814,948 KiB**, swaps **0**.

Both `#print axioms successful_packed_block_loop_canonical` and
`#print axioms successful_packed_decoder_canonical` report exactly
`[propext, Classical.choice, Quot.sound]`.

`successful_packed_decoder_canonical` requires only the literal source decoder
to return `ok (core.result.Result.Ok output)`. It proves all output words are
canonical, for arbitrary `N`. The block trace propagates zero invalid flags
backward and full-array canonicality forward, using the eight-word scanner
certificate and preservation of array positions outside each block. The entry
point starts from the canonical zero-filled array. Neither the 104-limb nor
48-limb case is concretely unrolled.

Earlier focused iterations corrected slice bounds and generated Rust Result
branch extraction; none failed for memory pressure. One unused simp-argument
warning remains in the zero-array proof and does not affect the theorem.

No full manifest replay was run. Gamma-combined query values, normalized fold
polynomial, and the R26 terminal `runningCanonical` premise remain outstanding;
this result is the source decoder bridge they require, not an end-to-end V7
release closure.
