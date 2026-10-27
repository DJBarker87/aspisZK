# D290 / D293 — V374 pre-sampling monitor abort

Target not yet established. **V374 remains OPEN/P.** The corrected marker-before-drain order ran, admission succeeded, and the capped monitor aborted before launching the sampler with **`[Errno 61] No data available`**. No timing samples were collected. No rerun or infrastructure repair was attempted.

Marker created **2026-10-27T14:30:17.507555+00:00**, fixed expiry **2026-10-27T14:55:17.507555+00:00** (1,500 seconds, never extended). Drain completed **2026-10-27T14:31:47.537843+00:00**, after 90.008 seconds and 4 inventories at 30-second intervals; no capped workload remained in the final inventory. The initial scope was `run-r1887c3b2f17746f2a8b6bb3e99f9072e.scope`, running `LPg_K022` in `codex-cx-leaf-p6-7-20261027`. **The exit trap removed the marker at 2026-10-27T14:31:47.697368+00:00; absence was verified again after the abort.** Sampling start/end: N/A.

Both binary hashes matched the preregistration before marker creation and were rechecked by the unchanged window entrypoint. No rebuild occurred:

- Harness: `ede68055604cce057f3d0b96fa575b06f30290bba4bcdb50493b7b81a797eb02`.
- Candidate: `161abfd8d155a2ccf35a461cd8e03fbf909e0f8b1c59efdddec1d76e74811472`.

The exact planned entrypoint ran with `QUIET_WINDOW_OWNER=1`. Admission JSON says `allowed: true`; scanner exit was 0 (its inspected source returns 0 iff allowed is true). The monitor scope had MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64, monitor CPU 0 and configured sampler CPU 2. Scope/entrypoint exit: 1; worker receipt status: 78. Worker wall: 0.000646227 s; cgroup memory peak: 6,631,424 bytes; swap peak: 0. This cgroup peak is not a process-RSS measurement. Sampler RSS/time and `#print axioms`: N/A; no sampler, Lean or Kani ran in this job.

The initial guard failed before `metadata.py`, leaving no sampling `host.json`, CSV, status counts or calibration observations. The post-abort diagnostic independently reproduced errno 61 on `/sys/class/thermal/thermal_zone6/temp`; that is the likely failed read, inferred from the guard order rather than a captured traceback. Other readable thermal sensors were below 90 C. `d293/post-abort-host.json` records CPU identity/microcode, kernel, CPU policies/topology, frequency/temperature, ASLR, lockdown, rustc and processes; it is explicitly a post-abort snapshot. Admission identity/policy assertions passed; resolved features/toolchain provenance remain in the prepared metadata. No assertion of a quiet sampling environment follows.

| Experiment | Raw class 0 / 1 | Held-out/cropped counts | Max absolute t | Verdict |
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

`results.json` retains each experiment and all 100 crop percentiles, with zero counts and unavailable cutoffs, first-order/centered-square statistics and maxima. Analysis was not run because there are no samples. **No detected-difference finding and no no-leak verdict can be made.** The preregistered rule remains |t| < 4.5 = no leak DETECTED at this sample size (not proof of absence); |t| ≥ 4.5 = timing difference DETECTED. An incomplete budget is not a pass.

**DOITM OFF (V371)** remains a substantive retained limitation under Secure Boot lockdown.

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

The D293-authorized fixed 1,500-second marker and marker-before-drain sequence supersede the plan's original 900-second marker scheduling. This orchestration change is recorded; no experiment ran non-conformingly. No implementation source, class, count, threshold or kernel changed. The evidence-only driver is retained as `d293/run-window.sh`; raw receipts are under `d293/window-1793111507/`. The previous D290 drain-before-marker failure remains in commit `30c33282ed` and `d290/`.

No premise was removed, added, weakened or moved into T. V374, V371 and every independent endpoint/deployment obligation remain retained. No keys or funds were involved.

Next deliverable: lead investigates the unavailable thermal sensor and supplies a reviewed monitor/configuration or new qualified schedule. Do not suppress the guard or rerun unchanged. Then collect the full preregistered samples, analyze once after marker removal, and review any threshold crossings.
