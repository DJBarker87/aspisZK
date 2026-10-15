# Typed recovered-word plumbing evidence

This focused Lean module defines a total map from optional packed C1/C2 leaf bytes to 29-lane initial words, using strict `MixedLeafDecoder.decodeC1`/`decodeC2` and zero defaults for missing or invalid leaf decodes. It proves unconditional `WordTyped` membership in lane-specific `RingHom.fieldRange` subfields and projections for successfully decoded C1 base lanes, C1 QM31 tail, and C2 QM31 coordinates. It does not connect Merkle `recoverAt` output, transcript positions, Rust callers, or any causal/source refinement.

The green target is `R1TypedRecoveredWords` attempt `typed-recovered-words-d`: exit 0, 1.64 s, 3,507,752 KiB peak RSS, zero swap, `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, `TasksMax=128`. Its five public theorem audits report `[propext, Classical.choice, Quot.sound]`. Attempts a–c are retained failed proof iterations.

The source SHA-256 is `85243ca24d3e9fc6272847244b77796cd3f7ea98397fc563783a212c6b8e1350`. Source base revision recorded for this focused task: `6459d24bcd83bf12441b606d8031b6c9301bc320`. The build used `/home/dombarker/project-offloads/aspis-r1-concrete-decoder-20261013` and the pinned `compile-snapshot.sh` wrapper. Imported source and object pins are listed in `source-manifest.json`; archived object hashes are listed there as well.
