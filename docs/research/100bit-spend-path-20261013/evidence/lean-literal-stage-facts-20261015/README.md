# Literal staged-reader plumbing evidence

This focused bundle records the staged Option projection lemmas and message-component congruence lemmas. It contains two successful focused compiles and one failed proof attempt, with the original source snapshots, receipts, logs, time records, and SHA sidecars preserved.

`R1LiteralStageFacts` proves that each successful later staged read exposes its earlier successful stage. `R1LiteralStageMessageCongr` proves that payload-stage readers and `vAt` depend only on message components when the projected message lists agree. The latter compile emitted three unused-simp-argument warnings; they are preserved in its output log.

Both successful compiles used `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, and `TasksMax=128`. The `R1LiteralStageFacts-a` attempt failed locally because the draft used nonexistent extension projection names; its five axiom reports include `sorryAx` and are excluded from successful audit counts. The final `b` attempt has five standard-only reports. `R1LiteralStageMessageCongr-a` has six standard-only reports.

The archive contains the two final `.olean` files and their direct import `R1LiteralOpeningStages.olean`; there are no loose `.olean` files in this bundle. `source-manifest.json` records exact source and object hashes. This evidence establishes only the stated reader plumbing.
