# R21 packet replay evidence

Date: 2026-09-22 (UTC)

## Targets and provenance

- Reviewed commit: `6f00e7f6c893c3a81bc37526e32d563434d303c8`.
- Packet: `docs/research/v8-full-view-zk-20260912/r21-pack`.
- Original packet was not used as a replay workspace. The fresh replay copy was
  `/home/dombarker/project-offloads/aspis-r21-replay-20260922-e68At0/r21-pack`
  on NUC `nuc` (`dombarker@100.108.41.90`).
- R20 control: `/home/dombarker/project-offloads/aspis-r20-clean-20260922-b`.
- Stage table input: `docs/research/v8-no-work-100-20260907/experiments/r17_basis_tables.rs`.
- Required ELF SHA-256:
  `fbaaab12e5f0e798dde28626abadb61cff69354cabb2dcf3f1125559efb2db8c`;
  remote `sbf-primary/aspis_v8_performance_sbf.so` matched.

## Integrity checks

- `MANIFEST.json`: 17/17 entries matched size and SHA-256.
- `SOURCE_PINS.json`: 5/5 reviewed Git blob IDs matched the reviewed commit.
- The local original packet remained unchanged after replay; generated files
  were copied into this evidence directory only.

## Replay commands

Both commands ran in the same systemd user scope with:

`MemoryHigh=2G MemoryMax=3G MemorySwapMax=0 TasksMax=128`

1. `python3 run_checks.py --ranks`
2. `python3 tools/generate_cycles.py --stage-table /home/dombarker/project-offloads/aspis-r20-clean-20260922-b/docs/research/v8-no-work-100-20260907/experiments/r17_basis_tables.rs`

The runner used `g++ -O2 -std=c++17` with the supplied sanitizer flags.

## Results

- Both exit statuses: `0`.
- `run_checks.py --ranks`: wall `35.63 s`, max RSS `174404 kB`, swaps `0`.
- `generate_cycles.py --stage-table`: wall `0.03 s`, max RSS `14608 kB`, swaps `0`.
- Cycle certificate: current rank `153`, candidate rank `89`; stage-table
  equality check passed.
- Rank screens: base and qm31 each reported `H1_rank=540`, `G_rank=601` for
  seeds 1 and 2.
- Control summary: `transport_basis_cases=1024`, `pad_images=89`,
  `arbitrary_correction_cases=128`, `changed_coordinates=163`,
  `nontrivial_cycles=74`, `correction_rank=89`, `max_cycle_length=4`.

Raw command output and `/usr/bin/time -v` records are in this directory.
