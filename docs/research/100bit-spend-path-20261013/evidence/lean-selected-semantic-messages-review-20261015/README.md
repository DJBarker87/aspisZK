# Selected semantic messages prepublication audit

The selected-semantic-messages bundle’s checksum list passes. Its two attempt snapshots match their source hashes, receipts, and sidecars; the green source matches the current worktree; the two direct import sources, all three archived objects, and runner pins match the manifest. The green log has four axiom reports containing only `propext`, `Classical.choice`, and `Quot.sound`.

Audit history: an initial review found that failed attempt `a`’s manifest listed zero reports while its preserved failed log contained three. fs corrected the manifest to three and added a failure audit note; the updated source-manifest hash and matching count are recorded in `review.json`. The original discrepancy remains in the audit history. Attempt `a` exited 1 and is not green evidence.

The inspected Lean interfaces retain their stated bounds. `SelectedTranscriptParams` accepts a raw message only with length at most 3717; its public-statement constructor explicitly requires a successful public parse. `SelectedChallengeMap` keeps rows 25 and 26 as raw QM31 parameters and separately proves the existing circle-parameter conversions. `SelectedSemanticMessages` handles typed semantic rows 0–24, and `toSemantic` takes `recoverC2` as an explicit callback. None asserts Rust refinement, full protocol acceptance, or a probability result.

The two source inventories’ pins match their cited sources. They also preserve the framing distinction: semantic records carry a P1 tag plus a 4-byte length before the payload, while opening transcript absorbs carry the 4-byte payload length without that P1 tag. The separate 2,784-byte `semantic_wire` row-25 layout is not conflated with the 3,712-byte S2 `r1_wire` row-25 payload.
