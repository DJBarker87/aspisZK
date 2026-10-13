# Actual P3 OS-mask proof: finite rank check

Root-run optimized NUC check, 2026-10-13. This checks one actual accepted
P3 Pool proof; it is not an R1 privacy theorem or good-challenge density bound.

The input is the fresh OS-mask transfer at 13 populated pairs, generated and
accepted by the P3 Pool harness. Proof SHA256:
`f04b11c9e5b725749ed8810c529cdeb25aab2161bca4dc3378647fc089b53ed3`.
Public ASF8 SHA256:
`f6bcd49446f1077d2c5ed4be940e91f0be444efc5ae83024ec0700b8c205c331`.
The probe parses the salted grammar, verifies the semantic prefix and derives
the actual transcript challenges and 22 query positions. It uses D18 transport
and the two K-valued G/D compensators for the actual WideExact gamma.

Results:

- all 16 eligible C1 raw maps have rank 112;
- balanced H1-padding map has rank 94 in ambient dimension 95;
- compensated pure round image has rank 1080;
- its initial-zero subspace has rank 1076;
- all 29 two-pad cancellation identities pass.

The gate ran with `--release --locked --offline --features private-leaf-salts`.
Compilation plus the named raw-map and pure-image elimination steps took
36.5363 seconds, exit 0; sampled aggregate RSS peaked at 1,621,225,472 bytes,
child maximum RSS 656,500 KiB, cgroup peak 1,307,774,976 bytes, swap zero.
The systemd scope enforced MemoryHigh 4 GiB, MemoryMax 6 GiB, MemorySwapMax 0.
The probe executable SHA256 was
`ea9c892f33e9cb3ce7e6378bf71383a74a5830c7fe0d5ae020365d7dfab07a6e`.

`transfer13.json` records the exact command and resource receipt;
`transfer13.log` records the public challenges, input hashes and ranks.
`inputs-sources.json` hashes the five probe inputs, and
`dependency-source-manifest.sha256` records the P3 dependency source tree.
`actual-Cargo.toml` records the dependency paths into that frozen source tree.
The only probe change from the earlier gate is forwarding the default-off
salted-proof feature; its rank algorithms are unchanged.
