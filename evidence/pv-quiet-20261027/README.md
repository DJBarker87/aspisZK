# D286 op223 timing gate: PASS

Measured on the integrated candidate with no implementation changes. This is fixture timing evidence on the pinned host; it removes no privacy theorem premise. Target not yet established.

Control: `c57a344726745387efb38d1571d885c69ce829ee`. Candidate: `8873306db187ec0b530d2469d4ec0f7f85e25365`. Branch: `codex/pv-quiet-20261027`.

Five matched pairs (D216 sample count), coins 100–104, fresh process per side per pair. Order alternates control/candidate then candidate/control. Each process proves and verifies transfer and withdrawal. CPU affinity is fixed to CPUs 0–21; the unchanged harness uses 16 workers. Features: `optimized-terminal,r1p-check,ct-host-prover`.

| Fixture | Control median (s) | Control p10 / p90 (s) | Candidate median (s) | Candidate p10 / p90 (s) | Candidate/control | Gate |
|---|---:|---:|---:|---:|---:|---|
| transfer | 14.384269 | 13.890455 / 14.503126 | 14.377724 | 14.302280 / 14.487975 | 0.999544969 | PASS |
| withdrawal | 14.239355 | 14.021793 / 14.497004 | 14.248479 | 14.043503 / 14.436893 | 1.000640703 | PASS |

Both candidate medians are strictly below 15 seconds, and both median ratios are <=1.10. p10/p90 use linear interpolation between inclusive sample endpoints. All 10 matched fixture pairs have byte-identical public.bin and proof.bin (20 file comparisons); all 20 before/after measurement guards are quiet. Full unrounded samples, commands, comparisons and gate calculations: [comparison.json](comparison.json).

| Binary | SHA-256 | Bytes |
|---|---|---:|
| control | `1975a5d1bbdf3ca3378bd3b905f6f387862937bf019321f6f3d315c9b2cdfea6` | 2570904 |
| candidate | `6f561a4dd4060e4b741adb5526c8af6a4a8725dbc90570ae3ae250021fea63e5` | 2572624 |

Preparation: optimized `cargo build --release --locked --offline -j 4`, one scope at a time, before the window. Exact exported inputs match both Git revisions (6,015 control files / 6,137 candidate files; source-verification.json). Both fixtures passed an additional outside-window byte comparison at coin 99. Prior op223 ELF/differential evidence is reused from evidence/pv-op223-20261027; no covered source changed.

The initial admission refusal, one omitted include-input compilation failure, and an inner-barrier reservation race are retained. The omitted tracked glue_gen.rs was supplied from each exact revision before the successful build; no implementation changed. Admission refusals waited three minutes. No failed compiler command was rerun with unchanged missing inputs.

The host became quiet after 544.425 seconds, within the 900-second limit. All 19 cgroup checks and systemd-cgls listings are retained. D286 explicitly authorized this job’s marker lifecycle, superseding the old plan’s prohibition on worker removal.

Window start: **2026-10-27T13:34:48.889+00:00**. Original expiry: 2026-10-27T14:34:48.889+00:00; never extended. Measurement process exit: **2026-10-27T13:39:35.919+00:00**. Marker removed by EXIT trap: **2026-10-27T13:39:35.920+00:00**; its absence was checked immediately after collection. The marker held the exact owner/purpose requested. HUP/INT/TERM also route through cleanup.

Host conditions: all CPUs used the powersave governor before and after. Per-CPU frequency snapshots ranged 400000–4231415 kHz before and 400000–4520257 kHz after (frequency was observed, not fixed). Load averages (1/5/15 min): 2.40/3.58/3.87 before; 4.92/3.85/3.86 after. Complete CPU, toolchain, frequencies, load and cgroup inventories are retained in cpu.txt, toolchain.txt, measurement/before.json, measurement/after.json and guard receipts.

Measurement scope: exit 0, wall 286.800 s, peak process RSS 694116 KiB, cgroup peak 745578496 bytes, swaps 0. Every build/proof scope used MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64. Per-process GNU time receipts and scope receipts retain exact target, source revision, exit, wall, peak RSS and swaps; #print axioms is N/A because no Lean ran. No Kani, dudect or V374 ran in this job.

Both job-owned Cargo target directories were deleted after the marker was removed (cleanup.json). Binaries and raw deterministic fixture outputs remain on the host; no keys were deleted. No binaries, proofs or raw ledgers are committed.

Premises before/after: unchanged. No deployed endpoint premise or T field was removed, added or weakened. This measured gate does not establish universal cost, proof-byte refinement or side-channel simulation. Real RunJoin, E1/E2, universal proof-byte refinement, OS-failure independence, L1/L2/L3, endpoint composition and deployment closure remain.

Next deliverable: lead review and record D286 as fixture timing evidence for the integrated candidate, then make the integration/adoption decision alongside the remaining substantive obligations. No source change or additional regression is proposed by this job.
