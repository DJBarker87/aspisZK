# SemanticPayloadView source-pin replay

This bundle records the single focused replay of `R1SemanticPayloadView` after adding contemporaneous source and object pins for its two direct imports. It repairs the source-association gap for this new compile only; the earlier `lean-semantic-payload-view-20261015` bundle is not modified, and no historical source provenance is claimed for it.

The replay compiled source SHA `63d8ee366a6ca1beb5c4de26110419ddcaf83f87efb8de9d3151e24c0ef6506b` at source base `1aca98e95c815befa58ed61e65cccd21c7bf10b9`. It exited 0 in 3.35 s, with peak RSS 3,573,576 KiB and zero swap under a 4G/6G/0-swap/128-task cap. The output reports eight declarations, each with only `propext`, `Classical.choice`, and `Quot.sound`.

The bundle contains the exact target and direct-import sources, the three compiled objects in a deterministic archive, the receipt/log/source snapshots, pinned runner files, and the replay-plan reference. `source-manifest.json` records all hashes; `SHA256SUMS` covers every file except itself.
