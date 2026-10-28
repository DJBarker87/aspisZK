# Direction probes

Classification under the requested two-control criterion: **over-approximation (false failures)**. Both false properties are explicitly FAILURE, not merely hidden behind an unrelated harness failure. No false PASS was observed. This bounded result is not a soundness proof for all properties; name sensitivity remains to be tested.

- KNC_K001: only `obs.is_none()` changed to `obs.is_some()`. Explicit `assertion failed: obs.is_some()`, 1/58 failed.
- KNC_K002: only `assert_eq!(i,NBZ_Q)` changed to `assert!(i >= 10)`. Explicit `assertion failed: i >= 10`, plus the original false failure of `obs.is_none()`, 2/49 failed.

Both retain K008 file placement, module/helper/harness/global names, unwind 4096, command switches and exact captured surrounding source. Paths for the isolated scratch workspace, target and temp directory necessarily identify this job. Cargo.lock was copied from the captured frozen lock, graph validation passed separately before each Kani run, and the lock hash is unchanged afterward. The false payload is impossible because the harness assumes `i < 10` and passes that same i as `Phase::Query(i)`; the observer is literally None.

Receipts: KNC_K001/receipt.json and stdout.log; KNC_K002/receipt.json and stdout.log; each KNC_K00n-graph-check.json and corresponding KNC_G00n receipt.

[
  {
    "attempt": "KNC_K001",
    "exit_status": 1,
    "wall_seconds": 17.24971803900553,
    "peak_rss_kib": "534292",
    "swaps": "0"
  },
  {
    "attempt": "KNC_K002",
    "exit_status": 1,
    "wall_seconds": 7.739853244973347,
    "peak_rss_kib": "424896",
    "swaps": "0"
  }
]
