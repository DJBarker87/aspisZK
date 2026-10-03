# R440 saved build audit

`audit_saved_build.py` independently checks the saved source-only clone, direct optimized driver compile, and one focused candidate fixture from `../` and `../../fixture/candidate-saved/`. It does not invoke Cargo, rustc, Charon, or the fixture. It reads receipts and logs only.

The audit verifies 1,169 tracked source entries, the two permitted overlay paths and hashes, three tracked symlink paths, zero shared regular-file inodes, no copied target cache, reviewed pin references, and the source/cache snapshots. It checks the exact 46 external libraries plus two PSM inputs, direct rustc argv bindings, unchanged input inventories, pinned checkout cleanliness, exit statuses, GNU time metrics, cgroup limits/peak/swap/OOM counts, candidate binary hash, and saved fixture LLBC hash/receipt.

Observed receipts report clone status 0; direct rustc status 0, 13.54 seconds, 1,569,908 KiB peak RSS, zero swaps, cgroup peak 1,828,773,888 bytes and no OOM events; fixture status 0, 0.07 seconds, 115,808 KiB peak RSS, zero swaps, no LLBC errors. The fixture LLBC SHA256 is recorded by the checker output.

Boundary: these artifacts establish diagnostic tool custody/build and one small fixture capture only. They do not prove general source semantics, source-to-model correspondence, theorem closure, or release/security adequacy. Formal axioms are not applicable to this tool build/capture.
