# R448 refill-branch component evidence

The promoted R448 source is byte-identical to the successful input saved in `run/source.lean`. The saved run log, receipt, and runner are included. `manifest.json` records the exact successful target and direct import hash.

R448 covers the `c.index.val = 8` refill branch when the remaining attempt budget is at most eight. It relates the source-shaped `limbRun` call trace, value and updated state/block/index to `scanAt` on the newly stepped block. This is a bounded source-shaped execution fact, not a probability or freshness result.

To avoid duplicating the preceding module chain, the direct R444 source is referenced from the prior [R447 initial-block evidence bundle](../r447-source-initial-block-law/README.md); the verifier checks that saved source copy and the currently promoted R444 source both match the R448 receipt hash. This component is awaiting combination with the R449/R450/R451 source-coupling milestone.

Run `python3 verify_evidence.py` from this directory for a read-only integrity check. No compiler rerun was performed.
