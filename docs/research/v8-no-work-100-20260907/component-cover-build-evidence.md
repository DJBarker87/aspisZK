# Component-cover continuation: execution and evidence boundary

Research parent: `9254b2416c3f8c3c488d0475a00d812fee836e00`.
Borrowed formal source: `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.
This setup changes no previous proof source, runner, evidence record,
protocol, production file or native package cache.

## Fresh NUC workspace

The task directory is
`/home/dombarker/project-offloads/aspis-component-cover.ZIUqzo`.
Its imported overlay is an immutable hardlinked copy of the frozen
`aspis-covered-family.rfQFkf` overlay. Only new target filenames may be
written. The five prior green source/output additions are now pinned
committed imports; old files must never be overwritten through their links.

The retained host preflight recorded load 0.38, 47,050,059,776 available
bytes and no active build scope. The unrelated approximately 16-GiB VM and
all services were left untouched. This is a point-in-time check, not an
ongoing capacity reservation. Root serializes every heavy job.

`bootstrap_component_cover.py` checked 349 source blobs against the new
research or borrowed revision and 349 retained compiled artifacts. It
included the last successful `CausalCoveredRecovery` output missing from
that run's preflight snapshot. The previous origin `f19673b4` and its earlier
nested origins are retained separately from this continuation's parent.

The remote metadata preflight passed all 698 artifact hashes and every
declared native package revision, without invoking Lean. The command and
hashes are retained in `experiments/component-cover-bootstrap-preflight.log`;
the initial resource reading is `experiments/component-cover-host-preflight.log`.

```
component-cover-initial-manifest.json SHA-256
5ada1fd379886e25c6845054a825aecf82145f9f9f896c3433b1036407396f45
run_component_cover_nuc.sh SHA-256
3ca08461281d836d1898786dcdb2a074089dbe89421f46b9eb81e35ac255f129
```

## Focused execution contract

After the root grants the serial build slot, upload only new sources and
use a fresh run tag:

```
ssh dombarker@nuc.local 'bash /home/dombarker/project-offloads/aspis-component-cover.ZIUqzo/run_component_cover_nuc.sh /home/dombarker/project-offloads/aspis-component-cover.ZIUqzo TARGET fresh-tag'
```

The established selected-cache profile is MemoryHigh 8 GiB, MemoryMax
10 GiB, MemorySwapMax 0, CPUQuota 200%, Lean `-j1 -M9500`. No cold package
build is authorized. Logs include the actual command/cgroup, wall time,
RSS, swaps, exit, source/output hashes and named axiom reports. Preserve
every failed source version before changing a target; failure is not
release evidence and does not justify an unchanged larger-cap retry.

Each successful new source/output becomes immutable in this task's state.
Every dependent run creates a fresh import manifest including those outputs.
Return successful and failed logs, manifests, exact source snapshots and
compiled outputs to the local evidence directory. No unchanged prior proof
suite is rerun to check a new leaf.

## Evidence scope

The new read-only `experiments/audit_component_cover_evidence.py` passed
current-source success for all seven targets:
`CoveredOriginalSymbols`, `CoveredOODGRS`, `CurveOODGate`, `SelectedOODGate`,
`CausalOODReduction`, `SelectedCopyLayout`, and `SelectedCopyLayoutRows`.
It hash-checks each actual imported source/output
closure and rejects missing artifacts or nonstandard axioms. The final
`component-cover-evidence.json` records seven green leaves and 41 named,
standard-only axiom audits. Every successful run exited 0 with zero swaps:

| Target | Green run | Wall seconds | Peak RSS (KiB) | Axiom audits |
|---|---|---:|---:|---:|
| `CoveredOriginalSymbols` | v1 | 3.23 | 6,856,640 | 7 |
| `CoveredOODGRS` | v4 | 10.89 | 6,838,648 | 7 |
| `CurveOODGate` | v1 | 2.94 | 6,831,432 | 6 |
| `SelectedOODGate` | v2 | 4.60 | 6,867,636 | 8 |
| `CausalOODReduction` | v2 | 3.32 | 6,879,464 | 5 |
| `SelectedCopyLayout` | v1 | 2.36 | 1,913,972 | 2 |
| `SelectedCopyLayoutRows` | v1 | 0.87 | 1,731,268 | 6 |

The receipt maps 35 remote artifact versions across 13 runs to exact local
bytes, with no unmapped artifact. Five failed checks remain diagnostics:
`CoveredOODGRS` v1–v3, `SelectedOODGate` v1 and `CausalOODReduction` v1.
The last two exact failed sources were reconstructed by reversing the
documented source edit and matched against their recorded preflight hashes;
they are retained in `experiments/component-cover-failed-sources/`.
They are **not** claimed to be automatic cached source snapshots. The runner
stores hashes and manifests, not historical source bytes.

`CoveredOODGRSTypes` is a separately retained type/instance diagnostic with
exit 0 and no theorem audits. Its source/output are pinned in later import
manifests, but it is excluded from the seven-proof/41-audit census. The audit
checks its resources, hashes and import closure without promoting it to a
proof result. Recheck the final record with:

```
python3 docs/research/v8-no-work-100-20260907/experiments/audit_component_cover_evidence.py --check-recorded
```

The same audit independently compares all 272 endpoint triples and 224
pattern cells against the pinned selected Rust constants, retaining their
136-link/tag order. This is small static metadata verification, not a field
enumeration or proof of Rust execution/slot-to-link rational correspondence.

An independent exact-rational check reconstructs the old local ceiling
directly from binomial ratios and collected scalar coefficients, then adds
`117077/(k−1)` once. It agrees with `component-ood-ledger.json`: the new
local reduction ceiling is approximately `2^(-104.3660531355444)`.
This concerns acceptance outside the retained pair of symbolic OOD
identities. The identity-branch mass remains symbolic; no family multiplier,
duplicate repair charge or global extraction allowance is inferred.

Its source-to-olean correspondence inherits the retained prior evidence:
hash equality is not a fresh compiler reproduction. Native package
revisions remain an explicit compiler/cache boundary, not a Mathlib replay,
Rust execution refinement or resource-bounded Fiat–Shamir theorem.

The proof body remains 40,282 bytes. These proof/model artifacts do not
measure CU or prover time, change public messages, establish full-view ZK,
or by themselves return a checked payment witness. Unsupported accepted
extraction failure terms remain explicit rather than receiving a numerical
allowance from the build result.
