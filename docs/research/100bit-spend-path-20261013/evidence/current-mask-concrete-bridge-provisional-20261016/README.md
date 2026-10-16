# Concrete mask bridge: provisional evidence

`ExtractedMaskSemanticBridgeConcrete` passed Lean 4.32 in attempt f. It
instantiates the generic extracted-mask theorem with the exact wide-field
algebra map and existing concrete packing basis. Both basis compatibility and
the final equality have standard-only axiom reports.

The source-input canonicality assumptions remain. Historical transitive
dependency records are still being completed, so this is provisional evidence,
not final source admission or the complete spend theorem.

The successful check took 2.96 seconds (2.996 controller seconds), with peak
RSS 4,052,352 KiB, zero process swaps and exit 0. The cgroup used MemoryHigh
4 GiB, MemoryMax 6 GiB and MemorySwapMax 0. Both reports contain only
`propext`, `Classical.choice`, and `Quot.sound`.

`proofs.tar.gz` preserves attempts a–f, the exact successful source and object,
the imported generic bridge, runners/environment, Wide and K1 cache-resolution
records, and the then-current historical queue/index. The original manifest
and checksums are embedded. The historical 102-item queue is an intermediate
census, not the full dependency-admission claim; further reachable project
imports are being reconciled separately.

`manifest.json` is the unchanged original manifest. `root-audit.json` records
independent hash/receipt checks and theorem review. The outer `SHA256SUMS` pins
these published files. See the [design and remaining obligations](../../design/J1-CURRENT-MASK-SEMANTIC-BRIDGE-20261016.md).
