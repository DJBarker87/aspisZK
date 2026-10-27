# D290 / V374 measurement admission abort

Target not yet established. **V374 remains OPEN/P.** No measurement was launched: the original 15-minute drain deadline expired with a PV batch Rust build and other capped workloads active. This is a plan-compliant pre-window abort, not a timing pass.

Drain wait: **2026-10-27T14:10:31.632562+00:00 to 2026-10-27T14:25:31.677316+00:00** (900.045 seconds). The first inventory observed an idle snapshot after 570.776 seconds; new jobs started before the final recheck. The remaining wait used the original deadline, not a reset. At expiry, `codex-pv-batch2-20261027/candidate/build-baseline-001` was running optimized Cargo compilation; S2W capped jobs also remained active. Raw inventories are in `d290/drain.jsonl` and `d290/recheck.jsonl`.

**Window start/end: N/A. Marker removal time: N/A; never created.** Final absence was verified at 2026-10-27T14:25:46.094531+00:00. No window directory, entrypoint log or marker-created receipt exists. The authorized 1,200-second marker was never needed; no window was extended.

Both binary hashes matched before the wait, with the harness reverified in the final-recheck driver. No rebuild occurred:

- Harness: `ede68055604cce057f3d0b96fa575b06f30290bba4bcdb50493b7b81a797eb02`.
- Candidate: `161abfd8d155a2ccf35a461cd8e03fbf909e0f8b1c59efdddec1d76e74811472`.

The remote read-only final-recheck gate exited 78 before marker creation/admission/sampling. Its local SSH-to-tee pipeline reported 0 because tee was the last command; that pipeline status is not admission. No capped scope was launched by this job. Sampling wall/RSS/swap and `#print axioms` are N/A. No Lean or Kani ran in this job.

| Experiment | Raw counts (class 0 / 1) | Held-out/cropped counts | Maximum absolute t | Verdict |
|---|---:|---:|---:|---|
| mask-m31 | 0 / 0 | 0 / 0 | N/A | Not run; no verdict |
| mask-qm31 | 0 / 0 | 0 / 0 | N/A | Not run; no verdict |
| mask-m31-reject | 0 / 0 | 0 / 0 | N/A | Not run; no verdict |
| mask-qm31-reject | 0 / 0 | 0 / 0 | N/A | Not run; no verdict |
| pole | 0 / 0 | 0 / 0 | N/A | Not run; no verdict |
| m31-inv | 0 / 0 | 0 / 0 | N/A | Not run; no verdict |
| qm31-inv | 0 / 0 | 0 / 0 | N/A | Not run; no verdict |
| compress | 0 / 0 | 0 / 0 | N/A | Not run; no verdict |
| seed-field | 0 / 0 | 0 / 0 | N/A | Not run; no verdict |
| seed-salt | 0 / 0 | 0 / 0 | N/A | Not run; no verdict |
| seed-field-zero | 0 / 0 | 0 / 0 | N/A | Not run; no verdict |
| seed-salt-zero | 0 / 0 | 0 / 0 | N/A | Not run; no verdict |

`results.json` records every experiment and all 100 preregistered crop percentiles with zero counts and unavailable statistics/cutoffs. There are no raw CSVs, calibration samples, outcomes or t-tests, and offline analysis was not run. **No detected-difference finding can be made, and no no-leak verdict can be made.** The threshold remains absolute t < 4.5 for no leak DETECTED at the sample size (not proof of absence), and >= 4.5 for a timing difference DETECTED.

**DOITM OFF (V371)** remains a substantive limitation. Pre-window host conditions are retained in `d290/host-before-window.json`: identity, microcode/kernel, governor/turbo/SMT topology, frequency/thermal snapshot, ASLR and running processes. These are not evidence of a quiet sampling environment.

Kernel-specific instruction limits remain as follows; no result was obtained for any of them:

- `mask-m31`: Harness only; candidate scalar sampler is inlined, no standalone symbol equivalence.
- `mask-qm31`: Harness only; candidate qm31 has real return-register and metadata differences.
- `mask-m31-reject`: Harness synthetic rejection diagnostic only; scalar boundary differs.
- `mask-qm31-reject`: Harness synthetic rejection diagnostic only; qm31 return-register differences remain.
- `pole`: Valid-shape scan/return prefix matches; full symbols differ in cold panic metadata; synthetic repeated slots.
- `m31-inv`: Nonzero arithmetic/return prefix matches; full symbols differ in cold panic metadata; zero excluded.
- `qm31-inv`: QM31::try_inv leaf matches; harness interval also has wrapper/Option check and M31::inv callee; zero excluded.
- `compress`: Compressor leaf matches normalized instructions; full intervals/callers and complete prover differ.
- `seed-field`: Harness predicate only; candidate inlines helper. No OS fill, short-circuit composition, retries or joint-law claim.
- `seed-salt`: Harness predicate only, independently measured salt role; no full-route equivalence.
- `seed-field-zero`: Synthetic failure diagnostic of harness predicate only; no OS or caller/retry equivalence.
- `seed-salt-zero`: Synthetic failure diagnostic of harness predicate only; no OS or caller/retry equivalence.

See `INSTRUCTION-EQUIVALENCE.md` for the exact static comparisons. Any later timing result speaks directly for the pinned harness interval; matched leaves cannot establish whole-candidate or shipped-route timing equivalence.

No source, class, count, threshold or kernel changed. No experiment was run non-conformingly. The user-authorized 20-minute marker would supersede the plan's requested 15-minute window, but it was never written. No wallet/account keys or funds were involved. No premise was removed, added, weakened or moved into T; V374, V371 and all independent endpoint/deployment obligations are retained.

Next deliverable: lead coordinates a genuine host drain and new authorized quiet window; execute the unchanged plan, retain raw samples/status/environment/monitor receipts, then run the preregistered offline analysis and review any threshold crossing.
