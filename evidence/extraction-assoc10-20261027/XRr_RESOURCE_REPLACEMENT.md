# Checkpoint symbolic split

L084 CheckpointShape.size hit the default heartbeat limit at whnf after exposing a large serialized prefix and its final length guard. Exit1; no proof/axioms credit; RSS2650132KiB,swap0,10.652941475s. It was not rerun unchanged and no heartbeat/depth/resource cap was increased.
Replacement: retain the exact prefix under XRr_CheckpointLayout.bytes and prove generic XRr_CheckpointFinalize.value/length over an opaque list. The dependent shape/attempts proofs apply those symbolic lemmas. The nominal byte expression is a read-only port of XRm_CheckpointLayout.bytes; no runtime serializer or cohort law is changed. Final passing receipts below are authoritative.
