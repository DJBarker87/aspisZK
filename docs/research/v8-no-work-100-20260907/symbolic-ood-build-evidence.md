# Symbolic OOD continuation: execution and evidence boundary

Research parent: `f0f46ffede8812252ac7cee9edf5547f228533d5`.
Borrowed formal source: `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.
This continuation reuses, but does not modify or replay, the previous green
proof sources and compiled artifacts.

## Fresh isolated NUC scope

Task directory:
`/home/dombarker/project-offloads/aspis-symbolic-ood.zZbNpg`.
The imported overlay is an immutable hardlinked copy of the frozen
`aspis-component-cover.ZIUqzo` overlay. Only new target filenames may be
uploaded; never overwrite an imported file through its hardlink.

The retained host preflight at 2026-09-09 23:38:11 UTC recorded load 0.01,
46,942,638,080 available bytes and no active build scope. The unrelated
approximately 16-GiB VM, existing system swap use and all services were left
untouched. Host capacity is a point-in-time reading, not a reservation.
Root grants each heavy job separately.

`bootstrap_symbolic_ood.py` checked 357 pinned source blobs and 357 retained
compiled artifacts. This includes the previous seven green target additions
and `CoveredOODGRSTypes`, retained only as a type diagnostic, not an eighth
proof result. The final previous output omitted from its own preflight was
checked against the previous green-output receipt and added to the new
manifest. The old research parent `9254b241` and earlier origins are preserved
separately from this continuation's `f0f46ffe` parent.

The remote metadata preflight passed all 714 artifact hashes and declared
native package revisions without invoking Lean. Its exact command is in
`experiments/symbolic-ood-bootstrap-preflight.log`; host readings are in
`experiments/symbolic-ood-host-preflight.log`.

```
symbolic-ood-initial-manifest.json SHA-256
5deb683b63262b20ffe0502f5ffbc29b711772e0f4f6a09c997c98dc196073d2
run_symbolic_ood_nuc.sh SHA-256
7ed329de2a9fa09f7c0d41589c3a466156081bf0d392357262883667388c80ad
```

## Focused execution contract

After the root grants the serial slot, upload only new target sources, then:

```
ssh dombarker@nuc.local 'bash /home/dombarker/project-offloads/aspis-symbolic-ood.zZbNpg/run_symbolic_ood_nuc.sh /home/dombarker/project-offloads/aspis-symbolic-ood.zZbNpg TARGET fresh-tag'
```

Each run uses MemoryHigh 8 GiB, MemoryMax 10 GiB, MemorySwapMax 0,
CPUQuota 200%, and cached Lean `-j1 -M9500`. No cold dependency build,
unchanged prior-suite replay or larger-cap retry is authorized.

The new runner refuses a target already in the frozen initial manifest.
It copies the attempted source to `fresh-tag-source.txt` and hashes that
copy before checking the target. Return this snapshot alongside the log,
per-run manifest and output artifact, including for failed attempts. The
source snapshot is distinct from the immutable import manifest; the previous
runner and previous evidence are unchanged.

Logs record exact source/output/runner hashes, command, actual cgroup limits,
GNU wall time, RSS, swap, terminal exit, and requested named axiom audits.
Preflight and postflight verify the import manifest. A green new target is
immutable within this scope; later manifests include its exact output hash.

## Final focused evidence

The final read-only artifact audit passed all eight current-source targets
and 53 named standard-only axiom audits. Every successful check exited 0
with zero swaps. Exact source/output/runner/manifest hashes and the actual
import closure are recorded in `symbolic-ood-evidence.json`.

| Target | Green run | Wall seconds | Peak RSS (KiB) | Axiom audits |
|---|---|---:|---:|---:|
| `SelectedCopyLinkBalance` | v2 | 6.02 | 1,995,332 | 12 |
| `CurveOODDerivative` | v3 | 3.20 | 6,835,080 | 6 |
| `FactorCoherence` | v2 | 3.61 | 6,834,728 | 7 |
| `SelectedFactorCoherence` | v11 | 4.28 | 6,869,112 | 5 |
| `RationalHelperIdentity` | v2 | 1.18 | 2,035,344 | 7 |
| `FactorIdentityCover` | v2 | 3.40 | 6,843,080 | 7 |
| `SelectedIdentityCover` | v1 | 4.18 | 6,862,172 | 2 |
| `CausalFactorReduction` | v2 | 3.34 | 6,875,788 | 7 |

The receipt maps 85 exact artifact versions across 25 attempted checks,
with no unmapped bytes. All 25 runner-created source snapshots match their
logged attempted-target hashes. The 17 failed attempts are preserved as
diagnostics, including `selected-factor-coherence-nuc-v6-diagnostic`, a
failed trace-state inspection under the same target. It is not a ninth
proof result. No failed file's partial axiom report is promoted to success.

Recheck the final record without invoking Lean:

```
python3 docs/research/v8-no-work-100-20260907/experiments/audit_symbolic_ood_evidence.py --check-recorded
python3 docs/research/v8-no-work-100-20260907/experiments/symbolic_factor_ledger.py --check-recorded
```

The audit independently reconstructs the binomial and rational arithmetic
in `symbolic-factor-ledger.json`. The local numerical ceiling remains
approximately `2^(-104.3660531355444)`, but the retained event is stronger:
an actual accepted same-Q reconstruction rooted in a pre-gamma factor that
satisfies both OOD identities. One `117077/(k−1)` exception replaces the
previous OOD exception; no additional derivative, content, factor-count,
query or repair charge is added. The remaining accepted factor mass stays
symbolic. This does not establish component recovery or a payment witness;
see [the continuation report](symbolic-factor-continuation.md).

## Resource and provenance qualifications

There was a recorded scheduling exception. At one-second journal resolution,
the capped `CurveOODDerivative` v1 scope ran from 23:48:39 to 23:48:42 UTC,
and `SelectedCopyLinkBalance` v2 ran from 23:48:40 to 23:48:46, on
2026-09-09. A grant/hold message race therefore caused approximately two
seconds of overlap. The journal excerpt and its command are retained as
`experiments/selected-copy-link-balance-scope-timing.log`; only the repeated
Started-command suffix was omitted from the excerpt. Both original complete
commands remain in their build logs. The two individual 10-GiB caps remained
in force, but no aggregate peak RSS was measured. The audit explicitly marks
this batch as not fully serialized; its timings are not presented as a
serialized performance comparison. Actual pre/post source and output
provenance are checked separately from this scheduling deviation.

The audit also detected one concurrent main-source update at
`V7Tag73CheckedRefinementFullFutureFreePath.lean`; its old manifest's local
main-worktree pathname no longer held the borrowed bytes. The exact
borrowed-`26a9` git blob is retained in
`experiments/symbolic-ood-import-snapshots/V7Tag73CheckedRefinementFullFutureFreePath.lean.pinned`
with SHA-256
`b6b196e9a78811ddc9c6b31a85ce57ed53dcfa08a10e569b3ec3a43099e9cd66`.
The new receipt maps the unchanged remote source hash to that retained
snapshot. Neither main, the frozen NUC overlay, prior manifests nor compiled
cache files were overwritten, and no proof was rerun. All 357 retained
compiled hashes still matched; the source fallback fixes artifact access,
not a mathematical or compiler mismatch.

Pinned source and compiled-byte equality inherit the retained prior
source-to-olean evidence; they do not constitute a new compiler reproduction.
The native package cache remains an explicit pinned-revision boundary rather
than a Mathlib rebuild. No protocol, verifier, public message or proof-body
change follows from these setup artifacts. The 40,282-byte proof limit,
zero grinding credit, full-view privacy and resource-bounded Fiat–Shamir
obligations remain unchanged. A symbolic OOD identity is not yet a recovered
payment witness.

## Existing separability cache inspected

The read-only source/cache map is retained in
`experiments/symbolic-ood-separability-cache.json`. Every listed source
matches borrowed revision `26a9cd47`, the inspected source bytes, and its
initial-manifest hash; every listed retained output matches that manifest.
No export or compiler invocation was necessary.

The narrow available chain is `V7ExactCorrelatedAgreementFactors` →
`V7ExactCorrelatedAgreementSmooth`. Cached downstream modules include
`Hensel`, `LocalFactors`, `FunctionField`, `FactorBudgets` and
`OuterSelection`, all with the same `V7ExactCorrelatedAgreement` prefix.
`Smooth` supplies the literal resultant certificate of one prime
positive-`Y` factor, its nonzeroness from the derivative guard, explicit
`X`/`Z` degree bounds, and specialization/simple-root implications.
`Factors.exactV7_curvePrimeFactor_derivative_ne_zero` uses the actual QM31
characteristic for parent `Y` degree below 113.

The two narrow imported source/output pairs are:

```
Factors source 112e16cd05454f76e65958025ed01fd45e07dd2cf0632ee5eb53e2170b4ad8f3
Factors olean  a1bc2bb031992498ab1a35a60cdeb4e7edef3c2741118db5966392d27712cf6c
Smooth source  af4f75fd298825dc5d14f8315136bfd9d7bd550831dad834aa00e422b7a35c8a
Smooth olean   1b3dd5de2af101d0ae07afb4afbb59883bf4affece2aeb5d010c6b4b0c5cdaf7
```

These existing results do not silently discharge the next source boundary.
`exists_exactV7_uniformSmoothEvaluationPoint` selects an analysis point;
it is not a theorem that the actual transcript OOD point is smooth. The
global/local prime-factor multisets retain multiplicity. No square-free
parent/product construction was found in this exact correlated-agreement
chain, so a nonzero resultant for each prime factor must not be promoted
to a nonzero resultant for an arbitrary repeated-factor parent. Any new
actual second-OOD bound must retain its fixed pre-OOD object and derive the
appropriate exceptional-point cardinality/interface.
The new primary identity-factor cover instead handles repeated/singular
parents directly and does not assume this smoothness condition. The regular
derivative branch is a secondary result, not another term in its ledger.
