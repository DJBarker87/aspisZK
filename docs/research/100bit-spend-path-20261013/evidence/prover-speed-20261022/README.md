# Prover profile receipts

All times are measurements on the shared `nuc` build host, not formal bounds. No shipped source, verifier or protocol changes.

Revisions: research `7f13d411b8f6af7dbd17d23e79fd24bf9998e913`; v2 resolved in build receipts. Scratch roots: `/home/dombarker/project-offloads/codex-cx-prover-speed-20261022/{research,v2}`. Cargo cache is private to that job and reused between builds. Project source compilation appears explicitly in build logs; no Lean is built.

To reconstruct the primary experiment in a new job directory, export each revision's `Cargo.toml`, `Cargo.lock`, `crates`, `programs`, `xtask`, `audit/poseidon-pair-probe/program`, and `docs/research/v8-r0-zk-20261009/{z4,c3,refine}`. The instrumentation script restricts its destination to this job's host path; adjust that explicit guard for a separately authorized directory. Run `instrument.py <scratch-root>`, then `augment.py <scratch-root>`, and copy `speed_profile.rs` into the cost-probe examples directory. Do not apply the patches to shipped source.

Run each build and measurement serially using the following scope prefix and `host_job.py <research|v2> <build|run>`:

```
systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64
```

The runner pins optimized `cargo build --release`, `-j4`, `--locked`, the optimized-terminal feature and either `r1p-check` or `ct-host-prover`. It rejects incorrect scope limits. `admission.json` snapshots finite populated caps against 55 GiB; the current runner also checks admission before child work. The initial runner used for research is preserved verbatim as `host_job-initial.py.txt`, with the initial separate admission snapshot. Source and tooling pin JSONs distinguish these versions.

`stdout.log` contains one JSON row per published proof. `stderr.log` contains one `SPEED_RESERVATION`, one `SPEED_CHECK_SPLIT` (lane preparation + conversion, extracted builders) and one `SPEED_CHECK` (public data, emit, combined conversion/build, extracted checker) per completed attempt. Rejected/early-failed attempts would require interpreting the corresponding missing-check path; this experiment observed none. `time.log` is GNU time for the whole process, including untimed fixture preparation and verification. Per-proof wall timings exclude both. Receipt JSONs include CPU, compiler, environment, exact commands, scope limits, cgroup peak/swap and one-second process/thread/RSS samples. A sample is not a peak-thread bound; inspect source as well.

Profiler tuples are `[inclusive_seconds, exclusive_seconds, calls]`. Nested labels must not be added as inclusive times. `summarize.py` requires exactly five proofs of each fixture per variant, checks strict/dense verification flags and length, associates checker records with attempts, and checks that exclusive phase sums match end-to-end wall time within 1 ms. Medians are computed independently, so the medians of phase rows need not sum to the median total.

Supplemental `*-fine-*` receipts add semantic transcript timers and the emitter's existing lift/QPrime/BCond phase timers. They run one pair per variant to fill those evidence gaps; they are not extra samples silently mixed into the five-run primary statistics. Fine source pins/diffs and distinct binaries identify this pass.

`hash-counts.json` is source-derived count analysis. SHA disassembly excerpts show SHA-NI instructions in the binaries, not measured dispatch frequency. No `perf` permissions or external profiler were needed: explicit timers were used. No instruction-count or allocator-time measurements are claimed.

Binaries, target caches, raw proofs, OS private seeds, keys and nonce ledgers are not committed. Public nonce ledgers remain on the host. No accounts were provisioned/funded, no wallet keys were deleted and no network publication occurred. Receipt hashes identify native artifacts retained on the host.
