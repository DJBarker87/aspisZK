# Append-binding map focused Lean evidence

This bundle preserves five focused attempts: `R1AppendBindingMap` attempts a and b failed during local proof plumbing; c is green. `R1SpendDataMap` append-a is a successful dependency refresh from unchanged source after its imported `SpendRelation` source/object changed. `R1SpendRelationMap` append-a is green with the sixth `Rspend` conjunct.

Green metrics:

- `R1AppendBindingMap` append-c: exit 0, 1.58 s, peak RSS 3,336,104 KiB, zero swap; five axiom reports, each using only `propext`, `Classical.choice`, and `Quot.sound`.
- `R1SpendDataMap` append-a refresh: exit 0, 1.40 s, peak RSS 3,329,472 KiB, zero swap; four axiom reports.
- `R1SpendRelationMap` append-a: exit 0, 2.58 s, peak RSS 3,343,748 KiB, zero swap; two reports using only `propext`, `Classical.choice`, and `Quot.sound`.

All attempts used `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, and `TasksMax=128`. Exact source snapshots, receipts, sidecars, logs, and timing files are included. The append-map and spend-data-map compile phase used commit base `94281d6fb07be39b7f70c0b8de115a092b86c4e2` together with the preserved updated `SpendRelation` dependency snapshot; `SpendRelationMap` compiled at `1aca98e95c815befa58ed61e65cccd21c7bf10b9`.

The deterministic object archive contains the two final targets and pinned immediate import objects. The formal results concern the Lean model and do not establish Rust refinement or a runtime append-tree invariant.
