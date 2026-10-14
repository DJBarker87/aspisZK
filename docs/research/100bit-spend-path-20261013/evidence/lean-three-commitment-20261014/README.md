# Focused three-commitment recovery evidence

Eight new components and one combined checkpoint compiled on the pinned
NUC workspace at base `eac8ca7d792be9438200ec839b30102a5204881d`.
The 19 retained attempts comprise nine final successes and ten failures.
Every attempt includes its exact source snapshot, receipt, output, time
log, and both hash sidecars. Final sources and compiled objects match the
successful receipts.

`R1ThreeCommitmentCheckpoint-three-commitment-checkpoint-a` exited 0 in
0.79 seconds, with 1,798,836 KiB peak RSS and zero swap. Its 28 reports
use only `propext`, `Classical.choice`, and `Quot.sound`. All jobs used
MemoryHigh=4G, MemoryMax=6G, MemorySwapMax=0, TasksMax=128.

The deterministic nine-object archive has SHA-256
`b7fcdb4806b43395dd7c77b90ab40a58713827a8eb29f62c119fe691d9b03c2b`.
`source-manifest.json` records every attempt and member hash;
`ROOT-VALIDATION.json` records the lead's independent audit. No runtime
source changed. These results prove the stated finite-table recovery
interfaces, not complete protocol security or Rust correspondence.
