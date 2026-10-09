# R-E2 CU estimate before verifier refactoring

Source: `3fb27a8ad` plus the counter/probe-only diff pinned by [source-manifest.json](re2/source-manifest.json). Recorded before memory or structured-weight changes. Both original fixtures accepted under instrumented native `r0_verify`.

**Dense-baseline estimate: about 1.034 billion CU. This is not a completed verifier CU measurement, a lower bound, or an upper bound.** R-E’s invalid-stack crash did not measure the verifier’s transaction cost. The required memory/weight work continues despite this estimate.

## Method

Single-thread, feature-gated `r0-op-count` records inclusive tower operations and exclusive outermost operations at the existing phase callback boundaries. Pricing uses exclusive counts, so an E multiplication is not charged again for its internal QM31/M31 arithmetic. E = WideExact; K = QM31; F = M31. Generic CodeField inversions are priced separately from inherent field inversions. SHA counts include padding: ceil((message bytes + 9)/64).

The SBF ELF performs N primitive operations minus a matching empty loop for N=64 and N=128. Each local LiteSVM transaction has a 1,400,000 CU limit; simulation and execution agree for all 108 distinct transactions. These are two calibration sizes, not repeated end-to-end measurements. The table uses N=128. Input operands are dense nonzero values; data-dependent reductions and different inlining/call sites can change cost. SHA calibration hashes 32 bytes, one padded compression, and includes syscall/marshalling overhead. Multiplying that cost by multi-block compression counts overcharges fixed syscall overhead; parser, allocation, branching, packing and some raw integer arithmetic are not priced. Therefore the estimate is explanatory only.

Primitive ELF SHA-256: `29b477b3d6c5fd32b965a118c6bd07b650c871c4645cb20d6402ff439b9c6307`. Full logs, return values and pairs: [primitive-costs.json](re2/primitive-costs.json).

## Measured primitive costs

| Primitive | CU/op, N=64 | CU/op, N=128 |
|---|---:|---:|
| EAdd | 112.047 | 112.023 |
| ESub | 104.172 | 104.086 |
| ENeg | 53.984 | 53.992 |
| EMul | 1,466.453 | 1,466.562 |
| ESquare | 913.500 | 913.781 |
| EMulK | 662.703 | 662.828 |
| EMulF | 143.000 | 143.000 |
| EInv | 2,120.016 | 2,120.008 |
| EInvGeneric | 3,100.516 | 3,100.508 |
| KAdd | 45.000 | 45.000 |
| KSub | 38.109 | 38.055 |
| KNeg | 27.000 | 27.000 |
| KMul | 334.250 | 334.414 |
| KSquare | 214.625 | 214.969 |
| KMulF | 67.000 | 67.000 |
| KMulC | 143.344 | 143.516 |
| KInv | 942.516 | 942.508 |
| KInvGeneric | 1,647.016 | 1,647.008 |
| FAdd | 13.000 | 13.000 |
| FSub | 11.047 | 11.023 |
| FNeg | 6.000 | 6.000 |
| FMul | 19.016 | 19.008 |
| FInv | 579.000 | 579.000 |
| FInvGeneric | 1,214.000 | 1,214.000 |
| FHalf | 6.016 | 6.008 |
| FMulPow2 | 20.031 | 20.016 |
| ShaCompression | 136.984 | 136.992 |

## Predicted phase costs

Headroom is limit minus predicted total; negative means the estimate exceeds the limit. Phase markers retain their original order (Merkle then V1 for each fibre).

| Phase | Transfer CU | Withdrawal CU |
|---|---:|---:|
| Parsed | 0 | 0 |
| Semantic | 1,212,822 | 1,209,193 |
| ChordClaims | 53,548,448 | 53,548,448 |
| Merkle(0) | 9,726 | 9,726 |
| V1(0) | 10,760,783 | 10,760,072 |
| Merkle(1) | 9,726 | 9,726 |
| V1(1) | 10,761,494 | 10,759,752 |
| Merkle(2) | 9,726 | 9,726 |
| V1(2) | 10,761,494 | 10,761,885 |
| Merkle(3) | 9,726 | 9,726 |
| V1(3) | 10,762,915 | 10,760,143 |
| Merkle(4) | 9,726 | 9,726 |
| V1(4) | 10,760,072 | 10,760,783 |
| Merkle(5) | 9,726 | 9,726 |
| V1(5) | 10,761,494 | 10,761,494 |
| Merkle(6) | 9,726 | 9,726 |
| V1(6) | 10,762,205 | 10,761,564 |
| Merkle(7) | 9,726 | 9,726 |
| V1(7) | 10,759,182 | 10,761,494 |
| Merkle(8) | 9,726 | 9,726 |
| V1(8) | 10,761,494 | 10,762,595 |
| Merkle(9) | 9,726 | 9,726 |
| V1(9) | 10,763,626 | 10,759,823 |
| Merkle(10) | 9,726 | 9,726 |
| V1(10) | 10,759,361 | 10,758,721 |
| Merkle(11) | 9,726 | 9,726 |
| V1(11) | 10,762,595 | 10,762,915 |
| Merkle(12) | 9,726 | 9,726 |
| V1(12) | 10,761,564 | 10,759,432 |
| Merkle(13) | 9,726 | 9,726 |
| V1(13) | 10,761,885 | 10,761,885 |
| Merkle(14) | 9,726 | 9,726 |
| V1(14) | 10,759,752 | 10,761,564 |
| Merkle(15) | 9,726 | 9,726 |
| V1(15) | 10,762,595 | 10,765,048 |
| Merkle(16) | 9,726 | 9,726 |
| V1(16) | 10,761,174 | 10,760,463 |
| Merkle(17) | 9,726 | 9,726 |
| V1(17) | 10,759,893 | 10,760,213 |
| Merkle(18) | 9,726 | 9,726 |
| V1(18) | 10,762,915 | 10,761,885 |
| Merkle(19) | 9,726 | 9,726 |
| V1(19) | 10,761,244 | 10,761,174 |
| Merkle(20) | 9,726 | 9,726 |
| V1(20) | 10,761,174 | 10,759,893 |
| Merkle(21) | 9,726 | 9,726 |
| V1(21) | 10,762,915 | 10,762,205 |
| V2 | 741,896,873 | 741,896,873 |
| **Total** | **1,033,623,952** | **1,033,613,497** |
| **Headroom to 1.3M** | **-1,032,323,952** | **-1,032,313,497** |
| **Headroom to 1.4M** | **-1,032,223,952** | **-1,032,213,497** |

Full per-phase inclusive/exclusive operation counts: [transfer](re2/counts-transfer-ops.json), [withdrawal](re2/counts-withdrawal-ops.json). The JSON includes every V1 and Merkle interval separately.

## Resources and preservation

Each job used its own scope: MemoryHigh=4 GiB, MemoryMax=6 GiB, MemorySwapMax=0; no cap increase. Aggregate reservations were checked against 50 GiB. Resource records retain exact commands, source manifest, wall time, sampled aggregate RSS, child peak RSS, cgroup peak and swap. The native counter build peaked at 1.07 GiB sampled aggregate RSS; the SBF calibration build at 0.65 GiB. Native count jobs and the calibration completed with exit 0 and zero scope swap.

No verifier arithmetic/check order, semantic formula, serialization, or prover was refactored for this estimate. Instrumentation is absent unless explicitly enabled and is rejected on SBF. `WideExact::mul_m31` is added only as an unused scalar primitive for calibration. The SBF build reports unused R0 library instantiations with oversized stacks, but none is reachable from the primitive entrypoint, which calls field operations only; the primitive transactions all finish successfully. This does not establish stack safety of `r0_verify`.

| Fixture | Bytes | SHA-256 |
|---|---:|---|
| transfer | 95712 | `31e7706cd23a58e57832ff54126ed78548cdc502733daafb7d82bbceade77858` |
| withdrawal | 95712 | `ad7ba69ea1b97af9eb4a657b71036ecccda8df5797ea0d0be740809ba7ae12e3` |
