# Quadratic causal reduction: checked two-leaf checkpoint

Research parent: `51692ed712ecb646b51e15e4b8e93e149a6b4014`.
Executed runner/overlay parent: `289d7356c78a4cd493fe61a54f9548f2a0c11298`.
Borrowed V7 source: `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.

This checkpoint contains two green leaves and six standard-only axiom audits.
Both first attempts passed; there are no failed attempts for these targets.
It is not completion of the full soundness task or of the actual OOD sampler
probability proof. The separate source sampler audit receives no theorem credit.

| Leaf / attempt | Audits | Exit | Wall (s) | Peak RSS (KiB) | Swap |
| --- | ---: | ---: | ---: | ---: | ---: |
| SelectedQuadraticReduction v1 | 2 | 0 | 3.07 | 6,865,048 | 0 |
| CausalQuadraticReduction v1 | 4 | 0 | 3.27 | 6,888,240 | 0 |

The receipt maps 61 exact artifact versions with zero unmapped bytes. Each
attempt has its immutable source snapshot, complete log and import manifest;
both current source/output pairs and all requested axiom declarations are
checked. Actual imported research/V7 source-and-olean closure and both
manifest checks are required, not inferred from status messages.

## Provenance and resources

All earlier checkpoints remain immutable. The immediately inherited
selected-family checkpoint's four source/output pairs and four metadata
files are checked against the new parent's committed bytes. Earlier
source-bridge, extension and seven-leaf checkpoints retain their own origin
pins and exact source/output hashes. Their audit counts are inherited, not
credited anew, and none of their theorem suites or Rust controls are replayed.
The original 397 source/397 output baseline and pinned-main fallbacks remain
unchanged. Native Lean 4.32.0/mathlib packages are a pinned cache boundary,
not compiler reproduction.

The shared `/home/dombarker/project-offloads/aspis-higher-y.fMoMeX` workspace
and runner retain their actual older research pin. Every new attempt records
the literal command, matching GNU/Lean terminal status and actual cgroup
settings: MemoryHigh 8 GiB, MemoryMax 10 GiB, MemorySwapMax 0, CPUQuota 200%,
Lean `-j1 -M9500`. The source parent is recorded separately, not inserted
retroactively into runner logs. No compiler, remote job, cold build or old
proof replay is invoked by the metadata auditor.

Remote access uses Tailscale `dombarker@100.108.41.90` with `BatchMode=yes`,
`ConnectTimeout=10`, `StrictHostKeyChecking=yes` and `HostKeyAlias=nuc.local`.
The alias is for pinned-key verification only. Unrelated NUC work, services,
VMs and concurrent main edits are untouched.

## Verification and mathematical boundary

From the research directory:

```sh
python3 experiments/quadratic-causal-audit.py --prepare-receipt
python3 experiments/quadratic-causal-audit.py --check-recorded
```

The first command rejects unmapped artifact versions. The second requires
the exact frozen two-target census, all discovered attempts for those targets,
both current leaves green and an exact match with the recorded JSON.
Its status is checkpoint-only; global error/allowance remain null and
`full_soundness_task_complete` remains false.

The causal theorem keeps the fixed polynomial's two-OOD-root indicator and
the explicitly complementary accepted factor mass in the result. It averages
the specified gamma/later-response ideal game; it does not average the actual
two OOD points or prove their source/Fiat-Shamir sampling law. No residual
branch is identified with successful extraction or silently discarded.
The separate `quadratic-ood-sampler-audit.md` source review is not included
among these six axiom audits. Full higher-Y coverage, actual authenticated replay and bounded-resource
payment extraction, Fiat-Shamir and full-view privacy remain separate gates.
