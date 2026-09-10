# Quadratic selected-family: checked four-leaf checkpoint

Research parent: `be7a1731bd4d71de50fa39767a53523bf0bc9ff0`.
Executed runner/overlay parent: `289d7356c78a4cd493fe61a54f9548f2a0c11298`.
Borrowed V7 source: `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.

This separate record does not alter any earlier checkpoint. All four leaves
are green with nine standard-only axiom audits; five failed attempts are
retained without green credit. The full soundness task remains open.

| Target | Checked attempt | Audits |
| --- | --- | ---: |
| QuadraticSelectedDegree | v4 green; v1-v3 failures retained | 4 |
| QuadraticSourceSharp | v1 green | 2 |
| QuadraticFamilyAssembly | v2 green; v1 failure retained | 1 |
| SelectedQuadraticCover | v2 green; v1 failure retained | 2 |

The retained receipt contains nine attempts and 76 exact artifact
versions, with no unmapped bytes. Every attempted source version maps to its
immutable runner-created snapshot, not an advancing draft pathname. Green
status requires the exact current source/output pair, requested standard
axiom reports and actual imported source-and-olean closure; failed attempts
retain complete logs, manifests, snapshots and terminal resource records.

| Green attempt | Wall (s) | Peak RSS (KiB) | Swap |
| --- | ---: | ---: | ---: |
| SelectedDegree v4 | 3.37 | 6,861,876 | 0 |
| SourceSharp v1 | 3.21 | 6,841,140 | 0 |
| FamilyAssembly v2 | 2.90 | 6,836,504 | 0 |
| SelectedCover v2 | 3.41 | 6,872,512 | 0 |

All four green attempts exited 0. SelectedDegree v1-v3, FamilyAssembly v1
and SelectedCover v1 remain failed diagnostics, including any partial axiom
output. All nine retained attempts have zero swaps and checked resource
contracts. The JSON records their exact terminal statuses and measurements.

## Provenance and resource contract

The preceding source-bridge checkpoint's three source/output pairs and four
metadata files are verified against their committed hashes at `be7a1731`.
The twelve-leaf and seven-leaf predecessors are verified through their frozen
receipts and source/output bytes. Their recorded audits are inherited, not
recounted as new work or rerun. The 397 source/397 output original baseline
and exact pinned-main fallbacks are unchanged. Native Lean 4.32.0 and mathlib
remain pinned cache boundaries, not reproduced package compilations.

The shared `/home/dombarker/project-offloads/aspis-higher-y.fMoMeX` overlay
was created at the older runner parent. Its historical pin is preserved in
all logs/manifests, separately from this checkpoint's research parent.
Only root-granted focused proof jobs may run. Actual per-attempt resource
checks require MemoryHigh 8 GiB, MemoryMax 10 GiB, MemorySwapMax 0,
CPUQuota 200%, Lean `-j1 -M9500`, and matching GNU/Lean terminal exits.
No compiler, remote job, cold build or old proof suite is run by this auditor.
Unrelated NUC activity and concurrent main edits remain untouched.

Remote access is through `dombarker@100.108.41.90` over Tailscale with
`BatchMode=yes`, `ConnectTimeout=10`, `StrictHostKeyChecking=yes` and
`HostKeyAlias=nuc.local`; the alias is only for pinned-key verification.

## Read-only verification and scope

From the research directory:

```sh
python3 experiments/quadratic-selected-family-audit.py --prepare-receipt
python3 experiments/quadratic-selected-family-audit.py --check-recorded
```

The generator rejects unmapped artifact versions. The recorded check requires
the exact root-frozen census, all discovered attempts for these targets,
and every required leaf green. Its completion status is checkpoint-only.
Global error/allowance remain null and the full soundness task remains
explicitly incomplete.

Degree and fixed-family statements are not a conditional sampler law or an
accepted-payment witness extractor. The OOD obstruction and exceptional
gamma set must be fixed from pre-OOD inputs; a family filtered using revealed
OOD points is not substituted. Sequential probability composition, remaining
higher-Y coverage, Fiat-Shamir, authentication and full-view privacy remain
separate obligations. Focused theorem reports supply the exact hypotheses.
