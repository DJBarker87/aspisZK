# Shared-point S2 contraction candidate (isolated measurement)

This directory records a reviewed but not runtime-adopted candidate for `Weights::pair`. It shares the `d2/d3` tensor contraction only for two-fold S2 calls whose row-0 and row-2 factors match in both dimensions; otherwise the original computation remains active. The local crate source is restored to the pinned baseline (`weights.rs` SHA-256 `eb55a5a9…1c8d81a`). The isolated candidate source is `source/weights.candidate.rs` (SHA-256 `68c90877…63262f63`), with its exact patch and a preserved non-release rustfmt-drift snapshot alongside it.

The native release differential is in the sibling [shared-point-contraction-differential bundle](../shared-point-contraction-differential-20261015/). It reports 72 pair/error comparisons, 1 passed and 0 failed, with 28.64 seconds wall time, 539,528 KiB peak RSS and zero swap.

The isolated SBF build used Solana `cargo-build-sbf` 3.1.13 / platform-tools v1.52 / rustc 1.89.0, features `pool-adapter,private-leaf-salts`, and a 4 GiB high / 6 GiB max / zero-swap / 128-task scope. It exited 0 in 4.504 seconds; cgroup peak was 162,471,936 bytes, sampled aggregate RSS 298,688,512 bytes, and swap 0. The ELF is 1,248,240 bytes with SHA-256 `7cf2fb3e…9dd255a`. The 34 `Stack offset` diagnostic lines match the adopted h2 build byte-for-byte.

The 13-pair v0 transfer gate reused the same previously generated OS full-mask proof/public fixture as the h2 comparison. Stage 1 accepted at 1,392,386 CU / 295 bytes, unchanged from h2. The terminal transaction accepted at 1,236,579 CU / 879 bytes, versus h2's 1,303,475 CU / 879 bytes. Simulation matched execution, and the recorded settlement checks passed. This reused fixture preserves the original proof's OS-random-mask provenance; the current run itself has no new mask draw.

Four larger reused-fixture runs also accepted and settled with rollover histories: transfer and withdrawal at 255 and 1,023 populated pairs. Stage 1 CUs matched the corresponding h2 cases. Terminal CUs were 1,302,702; 1,318,905; 1,299,650; and 1,315,691 respectively. Full per-case logs, input pins, proof hashes, transaction sizes, and settlement fields are recorded in `results/`.

| Reused-fixture case | Stage 1 CU (h2 → candidate) | Terminal CU (h2 → candidate) | Terminal bytes (h2 → candidate) | Settlement |
|---|---:|---:|---:|---|
| transfer, 13 pairs | 1,392,386 → 1,392,386 | 1,303,475 → 1,236,579 | 879 → 879 | accepted |
| transfer, 255 pairs | 1,392,164 → 1,392,164 | 1,369,686 → 1,302,702 | 912 → 912 | rollover settled |
| withdrawal, 255 pairs | 1,390,833 → 1,390,833 | 1,385,823 → 1,318,905 | 1,077 → 1,077 | rollover settled |
| transfer, 1,023 pairs | 1,392,237 → 1,392,237 | 1,366,505 → 1,299,650 | 912 → 912 | rollover settled |
| withdrawal, 1,023 pairs | 1,390,915 → 1,390,915 | 1,382,595 → 1,315,691 | 1,077 → 1,077 | rollover settled |

The first cost-gate wrapper attempt refused to run because its task output directory had been pre-created; no transaction or keys were produced. That attempt's logs are retained. The successful retry used a fresh task directory. All generated keypair files remain on the NUC in their task folders with mode 0600; no keys were copied into this bundle. The local workspace's source manifest records 751 source paths and confirms that `weights.rs` is the only source difference from the frozen h2 source copy.

This is measured cost and local settlement evidence for an unproved cost-probe path. It does not establish protocol correctness, semantic equivalence beyond the finite differential suite, or production readiness. Root review remains required before adoption.
