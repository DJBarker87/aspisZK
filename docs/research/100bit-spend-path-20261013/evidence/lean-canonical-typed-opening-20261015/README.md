# Canonical typed opening evidence

This module composes each existing C1, C2, or folded no-event recovery theorem with `CanonicalRecoveryStability.later_of_earlier`, specializes the accepted Merkle path to the existing six-level index geometry, and applies the strict leaf decoder. For C1/C2 it proves the corresponding recovered packed input decodes at the concrete leaf index. For folded leaves it proves the optional recovered packed bytes bind through the strict four-WideExact decoder, and that any original index mapping to that leaf projects to the decoded slot. All original frame, path acceptance, opening-read containment, length, trace consistency, query-budget, and bad-event premises remain explicit; each theorem adds only successful strict-decoder output.

These are modeled Merkle and codec statements. They do not establish correspondence to Rust source, verifier caller behavior, or a protocol security conclusion.

Final green target `R1CanonicalTypedOpening`, attempt `canonical-typed-opening-c`, exit 0, 2.21 s, peak RSS 3,527,268 KiB, zero swap; cgroup `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, `TasksMax=128`. Four public audits report `[propext, Classical.choice, Quot.sound]`. Attempts a and b failed and are preserved with snapshots, receipts, output, and timing.

Final source SHA-256: `0a045246dff9119b10c450ac6debcbce79bea3a866042d53ed5efe1e9b1d8543`. Imported source/object pins and runner pins are listed in `source-manifest.json`.
