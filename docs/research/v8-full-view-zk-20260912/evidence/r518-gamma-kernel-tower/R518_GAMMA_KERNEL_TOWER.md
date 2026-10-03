# R518 gamma kernel tower transport

The final focused target is `AspisR518GammaKernelTower/GammaKernelTower.lean`,
SHA-256 `577959debed0a88288fed071ffd5f8ea582b4d64fdabbb22cf6b5d4251f0c66c`.
It compiled on the pinned cached host with exit 0, wall 0:01.27, peak RSS
3,233,052 KiB, and zero swap. The exact source snapshot, receipt, raw log,
and all six `#print axioms` outputs are in `focus-records/`.

It transports the existing natural-channel `kernel_result` through R517's
quadratic-tower coordinate conversion. In particular,
`decoded_kernel_identity` identifies the decoded grouped natural-channel fold
with the corresponding fold of actual quadratic tower multiplication.

All six theorem reports contain only `propext`, `Classical.choice`, and
`Quot.sound`. Its imports are byte-checked R515 `SharedGammaDots` and R517
`GammaTowerCoordinates` (their source hashes are in the receipt).

## Boundary

This is a pure ring/channel transport result. It does not prove native u64
wrapping, arrays, optimized Rust, loop execution, the complete selected
preparation routine, callback execution, or source correspondence.
