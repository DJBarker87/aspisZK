Native-only Digest32 and combined readonly/caller-factoring gates.
Run: python3 verify.py (read/hash-only; needs repository Git objects).

The archive contains four Git-pinned source snapshots, all failed and accepted receipts, runtime/compiler/binary hashes, full logs, source-freshness records, raw/resolved dep-info, generated circle-table bytes with unchanged build.rs pin, both ordered hash traces, and the retained 1233-case baseline trace.

11 accepted targets include one compile-only examples target. All23 named checkpoint tests passed; its original wrapper105/Cargo0 mismatch is retained and reconciled without rerun. The earlier wrong-filter0test result is NOT a test gate. Native finite evidence does not establish source/runtime refinement, syscall semantics, universal counts, lifecycle, or CU. Lead's sole J1.R13 candidate artifact and no-increase CU gate remain OPEN.

Host workspace: /home/dombarker/project-offloads/aspis-r1-digest32-native-20261016.
Before counter binary retained at retained-native-binaries/before-counter; after at retained-native-binaries/after-counter. Binary hashes are in respective run receipts; no native binaries or dependency cache are committed.
