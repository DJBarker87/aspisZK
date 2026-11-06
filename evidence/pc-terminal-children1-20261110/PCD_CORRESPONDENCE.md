# PCD correspondence

No complete native-to-cohort row correspondence is claimed yet.

PCD_Error transcribes every constructor of solana-program-error 2.2.2, including BorshIoError(String).
It is a full-value carrier; there is no scalar ABI quotient or presumed injectivity.
Payload-preserving map lemmas are generic model laws; native enum association remains OPEN.

POOL:320 frozen pair_forest.rs:1388–1410:
- checked_add condition at 1389: PCD_LaneRef.checked_next; E001 opaque Option equality replaced in E002 by explicit matching.
- frontier condition at 1393–1400: PCD_LaneRef.frontier_step; its level<20 own-input domain is required by the native enumerate loop.
- return record at 1402–1411: PCD_LaneRef.finish_lane; PCD_LaneValue.finish_exact/tree_exact/metadata_frame.
- loop: PCD_LaneLoop.scan_done_iff and first_failure give symbolic induction and exact first rejection.
The native cut-to-loop association, machine-word/array/digest carrier relation and source-call association remain OPEN.
No field multiplication is reached by these reference steps.
No extracted post-loop explicit return is relied on: all three references are loop-free; the source loop's final Ok remains a native fold obligation.

PCA state/borrow scaffolding is read-only precedent. No conditional PCA theorem is treated as CLOSED.
PCD rows remain subject to complete Result/effect/frame/abort, SAME arguments, native controls and the combined gate.
