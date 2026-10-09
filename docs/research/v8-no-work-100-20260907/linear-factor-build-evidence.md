# Linear-factor continuation: execution and evidence boundary

Research parent: `6f1ebbe55fcc6fd008071329d5270aae0521cf9a`.
Borrowed formal source: `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.
All twelve new targets are GREEN, with 72 named standard-only axiom reports.
The final read-only receipt audit checks their current source/output bytes,
imports, resources and all 24 exact attempt snapshots. No prior green proof,
runner, manifest or production file is changed by this continuation.

## Fresh NUC overlay

The new task is `/home/dombarker/project-offloads/aspis-linear-factor.8SUGGL`.
Its imported overlay is an immutable hardlinked copy of the frozen
`aspis-symbolic-ood.zZbNpg` scope. Only new target filenames may be uploaded;
never overwrite an imported hardlink.

The metadata preflight checked 365 pinned source blobs and 365 retained
compiled artifacts, incorporating all eight previous green additions and
the inherited type diagnostic. The diagnostic is retained for provenance,
not recounted as a new theorem. The final previous output is added from its
green-output receipt because its own preflight cannot include that output.

The previous receipt's exact pinned fallback for
`V7Tag73CheckedRefinementFullFutureFreePath.lean` is carried directly into
the new manifest. Its local path is the committed `.lean.pinned` snapshot,
not the main-worktree pathname that advanced concurrently. The old source,
output and manifest bytes are unchanged. The source fallback's SHA-256 is
`b6b196e9a78811ddc9c6b31a85ce57ed53dcfa08a10e569b3ec3a43099e9cd66`.

```
linear-factor-initial-manifest.json SHA-256
a6c1ea8c94462ebe64d082c81a464d33141dc2c8ae79ecc44fcd7d512d082b17
run_linear_factor_nuc.sh SHA-256
ff4db59289e0f873ab2892ebf6f8dcf294966ec42a457f3cff0c09bec01093bb
```

All 730 remote artifact hashes and declared native package revisions passed
without invoking a compiler. The command is retained in
`experiments/linear-factor-bootstrap-preflight.log`.

## Resource and snapshot contract

The host preflight at 2026-09-10 00:18:39 UTC recorded load 0.46 and
44,650,979,328 available bytes. An unrelated V7 K14-provider scope was
actively using Lean and Lake, alongside the existing approximately 16-GiB
VM. Those jobs, services and system swap were left untouched. This is not
an idle-host assertion or a reservation; root checks current capacity and
grants every new proof job individually.

After an explicit grant, upload only new sources and run:

```
ssh dombarker@nuc.local 'bash /home/dombarker/project-offloads/aspis-linear-factor.8SUGGL/run_linear_factor_nuc.sh /home/dombarker/project-offloads/aspis-linear-factor.8SUGGL TARGET fresh-tag'
```

Each own focused scope uses MemoryHigh 8 GiB, MemoryMax 10 GiB,
MemorySwapMax 0, CPUQuota 200%, and cached Lean `-j1 -M9500`.
No cold dependency build or unchanged-suite replay is authorized.
The runner refuses a frozen imported target and snapshots every attempted
source as `fresh-tag-source.txt`. Return that snapshot, log, import manifest
and output artifact, including failed attempts. Source/output hashes,
actual command/cgroup properties, GNU wall/RSS/swap, terminal exit and named
axiom audits are recorded. Every successful dependent run pins the outputs
of previous green new targets and rechecks its import bytes before/after.

## Final focused results

Every row below has terminal exit 0, zero swaps and matching pre/post import
bytes. RSS is GNU-time peak KiB, not aggregate host memory. All 72 named
reports contain only `propext`, `Classical.choice` and `Quot.sound`.

| Target | Retained successful run | Wall seconds | Peak RSS KiB | Axiom reports |
|---|---|---:|---:|---:|
| MonicFactorOOD | [monic-factor-v3](experiments/monic-factor-v3.log) | 3.47 | 6846956 | 8 |
| SelectedMonicCover | [selected-monic-v3](experiments/selected-monic-v3.log) | 3.07 | 6863144 | 3 |
| PrimeFactorRegularity | [prime-regular-v2](experiments/prime-regular-v2.log) | 3.06 | 6832104 | 4 |
| RationalHelperSpecialization | [rational-specialization-v2](experiments/rational-specialization-v2.log) | 0.97 | 2028996 | 2 |
| PolynomialValueInterpolation | [polynomial-value-interpolation-nuc-v2](experiments/polynomial-value-interpolation-nuc-v2.log) | 1.35 | 2286360 | 6 |
| LinearFactorInterpolation | [linear-factor-interpolation-nuc-v1](experiments/linear-factor-interpolation-nuc-v1.log) | 1.27 | 2283752 | 4 |
| CircleGRSLinearity | [circle-grs-linearity-nuc-v2](experiments/circle-grs-linearity-nuc-v2.log) | 3.48 | 6755904 | 5 |
| SelectedGRSSubmodule | [selected-grs-submodule-nuc-v2](experiments/selected-grs-submodule-nuc-v2.log) | 2.93 | 6822760 | 5 |
| SelectedLinearFactorRecovery | [selected-linear-factor-recovery-nuc-v1](experiments/selected-linear-factor-recovery-nuc-v1.log) | 3.31 | 6842716 | 3 |
| SelectedCopyAliasCore | [selected-copy-alias-core-nuc-v2](experiments/selected-copy-alias-core-nuc-v2.log) | 1.64 | 2193508 | 12 |
| SelectedCopyAliases | [selected-copy-aliases-nuc-v2](experiments/selected-copy-aliases-nuc-v2.log) | 1.37 | 2193368 | 11 |
| SelectedCopyAliasQM31 | [selected-copy-alias-qm31-nuc-v2](experiments/selected-copy-alias-qm31-nuc-v2.log) | 3.42 | 6694940 | 9 |

The receipt maps 24 attempts and 85 artifact versions with no unmapped
bytes: twelve current-source successes and twelve failed diagnostics.
The failures are MonicFactorOOD v1/v2, SelectedMonicCover v1/v2,
PrimeFactorRegularity v1, RationalHelperSpecialization v1,
PolynomialValueInterpolation v1, CircleGRSLinearity v1,
SelectedGRSSubmodule v1 and each of the three copy-alias leaves' v1.
Every failure exited 1; none was a memory kill. The largest peak across
all attempts was 6,863,144 KiB, and every attempt recorded zero swaps.
Failed results, including any interim axiom output, are not release evidence.

SelectedMonicCover, SelectedGRSSubmodule and SelectedCopyAliasQM31 hit
concrete recursion limits and were repaired with generic/named symbolic
interfaces. The copy core's first attempt also hit a 200,000-heartbeat
normalization timeout; its symbolic proof/import repair retained that limit.
The other diagnostics were local type, rewrite or simplification issues.
No target was retried unchanged with a larger resource or recursion cap.
All exact attempted sources were runner-created snapshots; no inverse-edit
reconstruction was needed. Root's actual tags such as `monic-factor-v3`
remain verbatim, without inventing an absent `-nuc-` pathname.

Exact target source/olean/log hashes, named declarations, commands and
per-run imported closures are in [linear-factor-evidence.json](linear-factor-evidence.json).
The initial 730-artifact overlay grew to 753 preflight entries for the
last dependent target. Newly successful output bytes are pinned before
downstream imports; unrelated pending outputs are not treated as proofs.

## Read-only audit and scope

The final check is metadata-only and does not replay a theorem:

```
python3 docs/research/v8-no-work-100-20260907/experiments/audit_linear_factor_evidence.py --check-recorded
python3 docs/research/v8-no-work-100-20260907/experiments/linear_factor_ledger.py --check-recorded
```

The independent arithmetic check reconstructs the unchanged local ceiling
and the two new exact class counts. The `114687^2` OOD-pair count remains
conditional on the explicitly uninstantiated distinct-uniform sampler model.
The `28/(k-1)` term concerns fresh gamma hitting a fixed small good set;
the existence of the sparse branch is not asserted rare. Neither new class
count is promoted to a global extraction allowance.

Two existing native Mathlib modules requested for the copy proof,
`RingTheory.Polynomial.Wronskian` and `Algebra.Polynomial.FieldDivision`,
were available as both source and compiled output. The small read-only
hash/availability check is retained in
`experiments/linear-factor-native-copy-imports.log`, together with the
native Mathlib revision. It did not import the uncached old deployed-copy
registry or rebuild a package. These hashes are an availability/provenance
observation, not a replay of Mathlib's compilation.

Exact source/output hash checks inherit prior source-to-olean evidence;
they are not a compiler reproduction. Native packages remain an explicit
pinned-revision cache boundary, not a package replay. These setup artifacts
change no verifier operation, proof message or 40,282-byte limit. They make
no new claim about CU, prover time, full-view privacy, Fiat–Shamir or a
bounded extractor returning a checked payment witness.
