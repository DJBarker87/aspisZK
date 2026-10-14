# Unified experiment trace recovery: focused NUC evidence

This bundle checks the new connection from the actual prover-plus-verifier
experiment trace to the existing guarded row-32 decoder. It does not certify
all decoder cases, the complete Fiat–Shamir instance, Rust correspondence,
or the final security/privacy claim. See [the proof scope](../../UNIFIED-TRACE-RECOVERY.md).

Base revision: `95dbdcac6262261cf14cffcf28bd030df62f8b37`. The exact final source
snapshots and their hashes are recorded in `source-manifest.json`.

All 15 final focused targets passed. The combined checkpoint ran once after
its dependencies passed: exit 0, 1.46 s wall time, 3,528,556 KiB peak RSS,
zero swap. Its 46 axiom reports contain only `propext`, `Classical.choice`,
and `Quot.sound`. The pinned runner applies 4G/6G/0-swap cgroup limits and a
5000 MB Lean limit. Runner and environment hashes match the earlier bundle.

## Exact attempt history

The 35 source-snapshotted attempts comprise 15 failed iterations, five
superseded green iterations, and 15 final green targets. No failed snapshot
has been replaced by the final source. Green superseded attempts include the
verifier-only recovery/injection statements before adding arbitrary prior
queries and the actual experiment wrapper. All 109 reports across successful
attempts use only the allowed standard axioms.

| Target | Final attempt | Wall time | Peak RSS (KiB) |
|---|---|---|---|
| `R1RawRecordSplit` | `c` | 0:00.86 | 1810856 |
| `R1UnifiedPayloadStep` | `b` | 0:01.61 | 3542464 |
| `R1UnifiedProtocol` | `f` | 0:01.54 | 3543540 |
| `R1UnifiedSteps` | `b` | 0:01.63 | 3545436 |
| `R1UnifiedChainReads` | `a` | 0:01.54 | 3540724 |
| `R1UnifiedVerifier` | `d` | 0:01.50 | 3537992 |
| `R1UnifiedQueryReads` | `a` | 0:01.51 | 3538348 |
| `R1UnifiedTraceReads` | `a` | 0:01.63 | 3544748 |
| `R1UnifiedPhases` | `c` | 0:01.58 | 3547088 |
| `R1UnifiedPhaseRecords` | `c` | 0:01.60 | 3542428 |
| `R1UnifiedRecovery` | `b` | 0:01.72 | 3552676 |
| `R1UnifiedRhoInjection` | `b` | 0:01.74 | 3552508 |
| `R1UnifiedPrefixedReads` | `a` | 0:01.60 | 3541708 |
| `R1UnifiedExperimentInjection` | `c` | 0:01.53 | 3543736 |
| `R1UnifiedTraceCheckpoint` | `a` | 0:01.46 | 3528556 |

## Audit and scope

Root inspected all final statements and proof bodies and verified the
focused receipts. `ROOT-VALIDATION.json` records the independent artifact
audit: every attempt snapshot/receipt/sidecar agrees, final sources match
current files, timing and resource records agree, all 15 object archive
members match the manifest, and all 14 central runtime fingerprints remain
unchanged. The archive contains final objects only; no loose `.olean`s are
included. This uses the pinned compiled cache and is not a cold replay of
the entire historical release manifest.

Object archive SHA-256: `31cd41762c422a1f66d71abf4a1ba8c05017b4f677fc6f3c257d56e707a997a6`.

`SHA256SUMS` seals every other file in this directory. Exact commands and
environment are retained under `runner/`; attempt exit status, wall time,
peak RSS, swaps, and source hash are retained under `attempts/`.
