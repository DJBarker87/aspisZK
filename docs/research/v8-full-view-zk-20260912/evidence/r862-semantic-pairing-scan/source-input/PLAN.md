# R862 authorized semantic pairing scan plan

1. Copy this exact proposed workspace to a fresh NUC directory; retain the unchanged frozen r18 module and verify its SHA before build.
2. Run only `semantic-scan`: it creates `semantic-scan.tsv` containing all 699 candidate `(d,s)` old 222-vectors followed by the new requested scalar. It does not call the previous 69-case low-constancy check and does not execute rank/pivot elimination.
3. The generator keeps each old per-candidate `observations` call, which preserves its existing fold, top-tail, inactive-balance, and transport-roundtrip assertions. The new scalar contracts `coin_weights_into(z)` with the same inverse mask at `transport.order[128+3*i]`.
4. If a candidate has an all-zero old vector and nonzero appended scalar, record it and stop. If none exists, preserve the scan TSV and create a separate lead-reviewed source change for a 223-row Schur-complement/elimination using the old 222 minor as immutable input. Do not rerun old 222 rank or the low-constancy gate.
5. Run under one fresh systemd scope: MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, TasksMax=128. Use the inherited frozen R117 flags, `--release --locked --offline --jobs 1`, and existing Cargo cache. Before launch record aggregate reservations below 40 GiB.
