# Higher-Y continuation: checked seven-leaf checkpoint

Research parent: `289d7356c78a4cd493fe61a54f9548f2a0c11298`.
Inherited source/cache origin: `ed41b2537e7dad15ce8055d9e5524e337ee8b9a4`.
Borrowed formal source pin: `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.

The seven-leaf checkpoint is checked: 33 standard-only axiom audits, with
exact source/output/import receipts and all seven failed Lean attempts
retained. The full higher-Y continuation and global security endpoint remain
pending. Bootstrap and evidence auditing invoked no compiler; the focused
proof builds were run separately under the root's grants.

## Isolated workspace and provenance

Current SSH endpoint: `dombarker@100.108.41.90` over Tailscale.
Use `BatchMode=yes`, `ConnectTimeout=10`, `StrictHostKeyChecking=yes`, and
`HostKeyAlias=nuc.local`. The alias reuses the pinned host key only; network
traffic must use the numeric Tailscale address. The original bootstrap and
generic proof used the earlier local-DNS route before the user's change.
Fresh task: `/home/dombarker/project-offloads/aspis-higher-y.fMoMeX`.

The imported `overlay` is hardlinked from the frozen
`/home/dombarker/project-offloads/aspis-own-support.f6NQzi/overlay`.
Only new target filenames may be uploaded. Never overwrite an imported
hardlink or modify the preceding scope, manifest, evidence or cache.

The last successful source-game preflight had 793 entries. Its final green
olean is added from the frozen output receipt, giving 794: 397 source blobs
verified against the new research/borrowed git pins and 397 retained
compiled artifacts verified by exact hash. All nine preceding new leaves
and the missing-output dependency export are included, not replayed or
recounted as new work.

Both exact source fallbacks are preserved:

- `symbolic-ood-import-snapshots/V7Tag73CheckedRefinementFullFutureFreePath.lean.pinned`,
  SHA-256 `b6b196e9a78811ddc9c6b31a85ce57ed53dcfa08a10e569b3ec3a43099e9cd66`.
- `own-support-import-snapshots/V7Tag73ConcreteRestorationTraceInduction.lean.pinned`,
  SHA-256 `6a21a2a463ca4ed109e09ab7e629828e083cb5be13e3657ab185ee649784c9d2`.

No current main source is substituted for those bytes. Concurrent main
edits and unrelated NUC services/VMs are untouched. The mutable preceding
`green-outputs.json` is retained as an origin receipt, not copied into the
new scope as mutable run state. Snapshot and verification helper scripts
are copied unchanged.

```
higher-y-initial-manifest.json
46c0485b661719d093fa8392783e36f42f5f446fa95d54525f3e0438ff232ab1
run_higher_y_nuc.sh
5780e61b4d286905ab912bb6ab8e103a20908f78c11bea415db40a5fad110e52
bootstrap_higher_y.py
f988d96a60c96d3b1444025d42754d3e2ec53d86ec63851a84522013226b9d03
```

The remote check records `OVERLAY_PROVENANCE_PASS=794` and
`METADATA_EXIT=0`. Native Lean 4.32.0 commit
`8c9756b28d64dab099da31a4c09229a9e6a2ef35` and mathlib revision
`81a5d257c8e410db227a6665ed08f64fea08e997` remain the declared cache
boundary. This is inherited source-to-olean evidence with exact artifact
bytes, not compiler reproduction or a package replay.

## Resource and attempt contract

At 2026-09-10 06:19:30 UTC, the read-only host check recorded load 0.18,
46,807,662,592 bytes available and no active user build scope visible.
The approximately 16-GiB VM and existing services/host swap were untouched.
This observation is not a continuing reservation or whole-host idle claim.

Root grants every compiler job separately. Focused scopes use MemoryHigh
8 GiB, MemoryMax 10 GiB, MemorySwapMax 0, CPUQuota 200%, and Lean
`-j1 -M9500`. No cold build or unchanged proof-suite replay is authorized.

After an explicit root grant, upload only a NEW target source and invoke:

```
ssh -o BatchMode=yes -o ConnectTimeout=10 -o StrictHostKeyChecking=yes -o HostKeyAlias=nuc.local dombarker@100.108.41.90 'bash /home/dombarker/project-offloads/aspis-higher-y.fMoMeX/run_higher_y_nuc.sh /home/dombarker/project-offloads/aspis-higher-y.fMoMeX TARGET fresh-tag-nuc-v1'
```

The runner refuses frozen imported target names. Every attempt captures
an exact `fresh-tag-nuc-v1-source.txt` snapshot, log and import manifest.
Retain all three, including failures, plus the successful olean. A green
source/output pair is pinned into subsequent run-specific manifests.
Reports must distinguish terminal exit, wall/RSS/swap, standard-axiom
audits and actual import provenance from partial failed elaboration.

The metadata generator, run locally without invoking Lean, is:

```
python3 bootstrap_higher_y.py selected-own-support-game-nuc-v5-manifest.json higher-y-prior-green-outputs.json ../own-support-transfer.json
```

## Current checked and diagnostic evidence

SimplePolynomialRootRigidity v1 is green with three standard-only audits:
0.92 seconds, 1,919,440 KiB peak RSS and zero swaps. SelectedSimpleRootRigidity
v3 is green with four audits: 5.37 seconds, 6,815,616 KiB and zero swaps.
Both source/output pairs and complete attempt receipts are retained.

Selected v1 is a separate transport-only incident. The local SSH session
emitted no runner or Lean output; the DNS probe exited 255 and the stalled
local SSH was explicitly terminated with exit 143. Root independently found
no remote v1 runner/log before a fresh tag was used. This is not a Lean
failure, a missing proof manifest or evidence that a compiler started.
Selected v2 did run and exited 1 for a missing unnamed-section `end`, despite
printing four standard-only axiom reports; its full failed triplet remains
diagnostic-only. V2/v3 and subsequent transfers used Tailscale.

The complete checked checkpoint is:

| Leaf / green attempt | Audits | Wall (s) | Peak RSS (KiB) |
| --- | ---: | ---: | ---: |
| SimplePolynomialRootRigidity v1 | 3 | 0.92 | 1,919,440 |
| SelectedSimpleRootRigidity v3 | 4 | 5.37 | 6,815,616 |
| QuadraticSpecializationDeterminant v3 | 5 | 1.08 | 2,182,204 |
| QuadraticSpecializationKernel v2 | 8 | 1.40 | 2,423,732 |
| QuadraticSpecializationCount v3 | 2 | 3.26 | 6,836,492 |
| QuadraticSpecializationBasis v2 | 2 | 1.09 | 2,248,860 |
| QuadraticTwistObstruction v1 | 9 | 1.05 | 1,953,424 |

All seven green runs exited 0 with zero swaps. The current audited receipt
contains 14 Lean attempts (seven green, seven failed) and 50 exact artifact
versions with no unmapped entries, plus the distinct transport-only incident
and two Rust-control attempts. The failed Lean attempts are selected rigidity
v2, determinant v1/v2, kernel v1, count v1/v2 and basis v1; all exact source
snapshots, manifests and complete logs are retained. Partial axiom reports
in those failures are not credited. No resource limit was raised.

Sylvester and further nonsquare drafts are outside this checkpoint; the
continuation census stays open. Native source/olean availability for the
determinant, polynomial field division/roots and resultant imports was checked
read-only over Tailscale; no native cache was rebuilt.

The separate optimized Rust control has two retained attempts: v1 failed
before compilation because `rustc` was absent from the nonlogin PATH; v2
compiled and executed successfully. Its 15,625 restricted F5 families and
78,125 numeric determinant checks are not a universal specialization or
verifier-security theorem. The tagged binary was copied/hash-checked at
08:11:24 UTC after the run. Its SHA-256
`61951072b95b342a3afe93d803a76c56fb7d49c6dc921294b381344a011a8116`
is explicitly post-run retention, not an execution-time logged checksum.
See `quadratic-control-results.md` for the exact tested family and guards.

## Stopping point

`higher-y-evidence.json` records `checkpoint.complete=true` for the seven
listed leaves while retaining `target_census_final=false` and the overall
`pending` continuation status. Its companion `higher-y-transfer.json` maps
every retained artifact version. Recheck this precise checkpoint read-only:

```sh
python3 experiments/higher-y-audit.py --check-checkpoint
```

The stricter `--check-recorded` final-continuation mode deliberately rejects
while the full census remains open. Neither mode reruns Lean or Rust.
Failed source snapshots and the transport-only incident remain distinct.
No higher-Y coverage, sequential OOD sampler
law, checked payment witness, bounded extraction, Fiat-Shamir, full-view
privacy or global numerical security claim follows from this bootstrap.
