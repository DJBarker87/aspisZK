# Independent sampler bundle review

This review checked the two requested evidence bundles at source base `764bf20a6fe0392951b670f73748a54f70c9f272`. Both bundles' `SHA256SUMS` verify; current source files match the manifest pins; source snapshots, receipts, object archive hashes and archive member hashes agree. Their successful logs contain only the standard reported axioms `propext`, `Classical.choice`, and `Quot.sound`.

The repeated-pass theorem is for the existing UInt32-list/natural-number model. The selected transcript bundle fixes a 33-row mathematical `Params` record and bounded-message/public wrapper. Together with `SelectedSamplerRanks`, `SelectedChallengeMap`, and `SamplerBlockRank`, these are checked model equalities and arithmetic connections. They do not establish that the current Rust source loop supplies this exact model, nor prove a full transcript decision or security result. The detailed pin and scope results are in `review.json`.
