# H2 wide-parser larger rollover cases

This bundle records four local P3 pool-path settlement reruns against the h2 verifier ELF. Each run reuses the exact previously recorded proof and public ASF8 fixture, unchanged. The original P3 fixture records report OS `getrandom` full-mask provenance; these reruns do not draw fresh masks or regenerate proofs. The new CLI classification remains `UNPROVED R1 S2 POOL-PATH ACCEPTANCE MEASUREMENT`.

The paired stage1 and terminal transactions were accepted in all four cases. Every case exercised history rollover with 256 roots before the operation; the rollover page, history, selected lane, and marker matched expected settlement. Transfers used 912 terminal serialized bytes; withdrawals used 1,077. Stage1 used 295 bytes. Exact CUs, bytes, errors, and resource receipts are recorded in `large-cases-manifest.json` and the raw per-run JSON/log files.

| Operation | Pairs | Stage 1 CU | Terminal CU | Stage 1 / terminal bytes | Result |
|---|---:|---:|---:|---:|---|
| transfer | 255 | 1,392,164 | 1,369,686 | 295 / 912 | accepted; settled |
| withdrawal | 255 | 1,390,833 | 1,385,823 | 295 / 1077 | accepted; settled |
| transfer | 1023 | 1,392,237 | 1,366,505 | 295 / 912 | accepted; settled |
| withdrawal | 1023 | 1,390,915 | 1,382,595 | 295 / 1077 | accepted; settled |

The h2 verifier ELF SHA-256 is `ea9be844a7027f613cf310c5fedd54c8db9e6d669ba325af46d3b5908ef43796`. Pool, registry and gate pins are in the manifest. Each run used a separate systemd user scope with MemoryHigh 4 GiB, MemoryMax 6 GiB, and MemorySwapMax 0. The sampled aggregate RSS, cgroup peak, exact argument vector, wall time and exit status are preserved in the per-run resource JSON.

The run task directories were kept on the NUC with restrictive directory/file permissions. Only public proof and public-input fixtures plus output evidence are copied here; private test keypairs are excluded and retained outside this evidence bundle.

See sibling `wide-parser-unrolled-v152-sbf-20261015` and `wide-parser-unrolled-v152-cost-20261015` for the h2 build and initial 13-pair cost gate. This bundle does not rerun those gates or change runtime source.
