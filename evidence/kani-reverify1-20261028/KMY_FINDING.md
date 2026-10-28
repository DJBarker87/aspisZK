# KMY window re-verification

Frozen revision: `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`. Frozen lock SHA-256: `5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef`.

Stage 1: original assertions and copy lengths under inspection. No credit restored yet.

Budget: Kani 0/60, Lean 0/60, Rust 0/5. Host scopes: MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64; one at a time. Existing launchers only. No release source changes.

## Stage 2: expand_values

LPn_K001: window PASS KMY_K006 (explicit validated loop, 16 bytes, arbitrary offset 0..80 in 96 arbitrary bytes); zero window PASS KMY_K007; original slice pointer/length premises PASS KMY_K008. L002 compiles `LPn_step_frame`, exactly the original byte assertion. Source correspondence: the frozen body has one 16-byte copy followed by one 16-byte fill for its sole admitted chunk. `KMY_expand_values.frozen.rs.txt` retains that body. No Rust-to-Lean compiler refinement is claimed.

K001 unsupported own option; K003 missing own PATH entry; neither reached verification. K004 passed but optimized trace did not reach the replacement: excluded from mitigation credit. K006 explicitly calls the identical validated loop. L001 failed draft; L002 has only propext, Classical.choice, Quot.sound.

## Stage 3: wide_view

LPa_K015 remains OPEN. KMY_K009 explicitly reaches the validated loop but the arbitrary 32-byte window over all 57,607 backing bytes times out at 90 seconds (6,473,584 KiB peak RSS). KMY_K010 splits after the copy, retaining the frozen wide_view body and original pointer/layout assertions; it also times out at 90 seconds. No counterexample was produced. Neither is rerun unchanged. Remaining split: prove the 32-byte region and exterior frame separately, then split parse rejection/value acceptance from view slice layout.

## Stage 4: six-wide serializer windows

KMY_K011 PASS: actual frozen WideExact serializer, canonical arbitrary eight limbs, all 32 encoded bytes, then a validated 32-byte copy into arbitrary pre-state at arbitrary offset in a 64-byte parent. Every exterior byte is framed. KMY_K012 PASS: arbitrary four-byte limb window and shift/byte projection. KMY_L003 compiles `wide_six`: six 32-byte windows give exactly `raw[j/32][(j%32)/4][j%4]` for every j<192. It also compiles append length/value and joined-digest composition. All axioms accepted.

The source overlays are generated from the frozen revision by KMY_prepare_serializers.py; only the module path and explicit validated copy calls change. Original and overlay SHA-256 values are in KMY_serializer_sources.json. These remain value-level composition results; allocation/growth integration is still a separate obligation for the Vec harnesses.
