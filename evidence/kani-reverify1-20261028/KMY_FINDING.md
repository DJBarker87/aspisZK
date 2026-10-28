# KMY window re-verification

Frozen revision: `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`. Frozen lock SHA-256: `5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef`.

Stage 1: original assertions and copy lengths under inspection. No credit restored yet.

Budget: Kani 0/60, Lean 0/60, Rust 0/5. Host scopes: MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64; one at a time. Existing launchers only. No release source changes.

## Stage 2: expand_values

LPn_K001: window PASS KMY_K006 (explicit validated loop, 16 bytes, arbitrary offset 0..80 in 96 arbitrary bytes); zero window PASS KMY_K007; original slice pointer/length premises PASS KMY_K008. L002 compiles `LPn_step_frame`, exactly the original byte assertion. Source correspondence: the frozen body has one 16-byte copy followed by one 16-byte fill for its sole admitted chunk. `KMY_expand_values.frozen.rs.txt` retains that body. No Rust-to-Lean compiler refinement is claimed.

K001 unsupported own option; K003 missing own PATH entry; neither reached verification. K004 passed but optimized trace did not reach the replacement: excluded from mitigation credit. K006 explicitly calls the identical validated loop. L001 failed draft; L002 has only propext, Classical.choice, Quot.sound.
