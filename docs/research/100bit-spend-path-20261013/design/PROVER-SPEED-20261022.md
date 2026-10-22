# Prover speed investigation — 2026-10-22

## Scope and stages

Measurement and analysis only. No shipped source changes, no Lean, no implementation or protocol adoption. Target: strictly under 15 seconds per proof, alongside the existing security contract.

Stage 1: pin research `7f13d411b8f6af7dbd17d23e79fd24bf9998e913` and v2 `2b7a80b65a` (resolved full revision in receipts), prepare scratch instrumentation and capped host runner. Stage 2: optimized repeated measurements, at least five transfer and five withdrawal proofs per variant, phase and retry accounting. Stage 3: rank proposals and assess proof bytes, source bindings, trust and L1/L2/L3 effects; stop.

Host: `dombarker@100.108.41.90`, dedicated job directory `/home/dombarker/project-offloads/codex-cx-prover-speed-20261022`. Every build/run is admitted within MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64. Cargo uses release and -j4. Expected heavy work: proof generation, including encoding and named P_R1 certificate generation/elimination, following a separate compilation stage. No dependency rebuild for Lean and no wallet key cleanup.

Measurements will use `prove_masked_retrying_with` and `generate_for_mask_nonce` with fresh public nonce identifiers and fresh OS private seeds. Fixture preparation and verification are outside the proof timer. These identifiers exercise the proof-account nonce interface but do not create, fund or publish Solana accounts; account provisioning and network publication are outside this measurement.

Evidence: `../evidence/prover-speed-20261022/`. Instrumentation is applied only to host scratch copies of pinned sources. Timings are measurements, not formal bounds or security evidence. Estimated savings will be explicitly labelled projections, not measured optimized results.

## Results

Pending.

## Ranked proposals and security consequences

Pending.
