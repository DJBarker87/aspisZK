# S3 inactive row composition v1

This focused theorem composes the emitted `Variant::row` result with the checked inactive helper and the grouped S3 classification. The input is explicitly `16*j+s`; the caller connection to optimized `Weights::pair` / `Weights::raw` is not established by this packet.

The Lean source is under `lean-candidates/s3-s9-current-repin-20261020/s3-row-inactive-compose-v1-20261020/sources/`. `manifest.json` records the source and import owner pins; `worker-manifest.json` preserves the original focused worker manifest. Attempt logs, preflight, receipt, and timing are copied under `attempt-v1/`. No `.olean` or other compiled binary is included.

The focused local Lean 4.32.0 check exited 0 in 16.57 s, peak RSS 2,224,209,920 bytes, swap 0; `#print axioms` reported only `propext`, `Classical.choice`, and `Quot.sound`. A later NUC admission rejection occurred before Lean launch and is retained only as a resource diagnostic in the worker directory; it does not alter this green local receipt.
