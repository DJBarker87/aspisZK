# Denominator continuation: execution and evidence boundary

Research parent: `2f6d82fef294410367aa1781fb924af7c38deab9`.
Inherited cache/source origin: `6f1ebbe55fcc6fd008071329d5270aae0521cf9a`.
Borrowed V7 formal pin: `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.

All ten new targets are GREEN, with 56 named standard-only axiom reports.
The final read-only audit verifies current source/output bytes, exact imports,
resources and all 20 attempt snapshots. No prior green source, output, runner,
evidence or production file is changed. Metadata audit invokes no compiler.

## Immutable imported workspace

NUC: `dombarker@nuc.local`.
Task: `/home/dombarker/project-offloads/aspis-denominator.QNcd5G`.

The overlay is a new hardlinked copy of the frozen
`aspis-linear-factor.8SUGGL/overlay`. Only new target filenames may be
uploaded. Never overwrite imported hardlinks or edit the previous scope.

Bootstrap verifies 377 source blobs against the new research commit or
borrowed V7 pin and 377 retained compiled artifacts against their exact
recorded bytes. All twelve preceding green outputs are included; the last
one is added from the previous green-output receipt because its own
preflight cannot contain its subsequent output. The baseline is therefore
754 entries, with no pending imported olean.

The inherited exact source fallback
`symbolic-ood-import-snapshots/V7Tag73CheckedRefinementFullFutureFreePath.lean.pinned`
is carried directly, with SHA-256
`b6b196e9a78811ddc9c6b31a85ce57ed53dcfa08a10e569b3ec3a43099e9cd66`.
Main's three concurrently modified V7 files and unrelated result directory
are preserved; no drifted main source is substituted into this overlay.
All retained local source/artifact paths checked at bootstrap match.

```
denominator-initial-manifest.json SHA-256
5ab9cfe6a223e1a956e55a56cda678f72f2b758ea9e89aa94b4db3eb1472550d
run_denominator_nuc.sh SHA-256
4a9ee5f24b89642c6a323db95dde0cded2097769c141ed6eb4dcdd16ef8d8935
```

The source/output provenance is inherited exact-byte evidence, not a
compiler reproduction. Native packages retain their recorded revisions
and cached artifacts; no cold dependency build or package replay occurred.
The previously inherited Types diagnostic is preserved, not counted as a
new theorem.

## Resource and attempt protocol

At 2026-09-10 01:06:54 UTC the host read-only check recorded load 0.24,
46,836,232,192 available bytes, and no active build user scope visible.
The existing approximately 16-GiB VM, services and host swap were untouched.
This observation is neither a continuing reservation nor a whole-host
idle assertion. Root grants every compiler job after checking capacity.

After an explicit root grant, upload only new target sources and run:

```
ssh dombarker@nuc.local 'bash /home/dombarker/project-offloads/aspis-denominator.QNcd5G/run_denominator_nuc.sh /home/dombarker/project-offloads/aspis-denominator.QNcd5G TARGET fresh-tag'
```

Every own job uses MemoryHigh 8 GiB, MemoryMax 10 GiB, MemorySwapMax 0,
CPUQuota 200%, and cached Lean `-j1 -M9500`. The runner refuses an imported
target. Each attempt snapshots its exact source as `fresh-tag-source.txt`;
return that snapshot, log, import manifest and successful output. Failed
attempts stay retained and never count as proof evidence. New green source
and output hashes become immutable prerequisites for later snapshots.

Per-run receipts record exact source/olean hashes, executed command,
actual cgroup properties, GNU wall/RSS/swap, terminal exit, standard-axiom
reports and pre/post byte checks. Missing or changed evidence keeps the
final audit pending. No unchanged theorem suite is replayed.

## Final focused results

All rows have terminal exit 0, zero swaps and matching pre/post imported
bytes. RSS is GNU-time peak KiB, not aggregate host memory. All 56 named
axiom reports contain only `propext`, `Classical.choice` and `Quot.sound`.

| Target | Successful retained run | Wall seconds | Peak RSS KiB | Audits |
|---|---|---:|---:|---:|
| LinearDenominatorPrimitive | [linear-denominator-primitive-nuc-v2](experiments/linear-denominator-primitive-nuc-v2.log) | 1.21 | 2423796 | 3 |
| GammaConstantLinear | [gamma-constant-linear-nuc-v2](experiments/gamma-constant-linear-nuc-v2.log) | 3.37 | 6837480 | 7 |
| SelectedGammaConstantRecovery | [selected-gamma-constant-recovery-nuc-v1](experiments/selected-gamma-constant-recovery-nuc-v1.log) | 2.94 | 6828892 | 1 |
| LinearMessageFamily | [linear-message-family-nuc-v1](experiments/linear-message-family-nuc-v1.log) | 3.17 | 6839588 | 3 |
| LinearDenominatorOOD | [linear-denominator-ood-nuc-v2](experiments/linear-denominator-ood-nuc-v2.log) | 3.07 | 6835712 | 4 |
| LinearDenominatorFactors | [linear-denominator-factors-nuc-v2](experiments/linear-denominator-factors-nuc-v2.log) | 3.34 | 6842148 | 5 |
| LinearDenominatorRegression | [linear-denominator-regression-nuc-v2](experiments/linear-denominator-regression-nuc-v2.log) | 3.18 | 6837504 | 6 |
| SelectedLinearCover | [selected-linear-cover-nuc-v6](experiments/selected-linear-cover-nuc-v6.log) | 3.29 | 6868460 | 8 |
| EarlyC1CopyCollisionCore | [early-c1-copy-collision-core-nuc-v1](experiments/early-c1-copy-collision-core-nuc-v1.log) | 1.03 | 2036044 | 7 |
| EarlyC1CopyCollision | [early-c1-copy-collision-nuc-v1](experiments/early-c1-copy-collision-nuc-v1.log) | 3.29 | 6714300 | 12 |

The receipt maps 20 exact attempts and 71 artifact versions with zero
unmapped entries: ten successes and ten failed diagnostics. Failures are
Primitive v1, GammaConstantLinear v1, OOD v1, Factors v1,
SelectedLinearCover v1–v5, and Regression v1. Each failure exited 1.
All 20 runs recorded zero swaps; the maximum peak was
6868460 KiB.
No failed or interim axiom output counts as release evidence.

The selected bridge's concrete recurrence/definitional-equality recursion
was replaced by a generic P-abstract message consumer. The five failed
sources retain the same recursion/heartbeat limits as the green replacement;
neither the resource cap nor proof limits were raised. The other failed
attempts were local type/rewrite/coercion glue, not memory kills. Every
attempt has its runner-created exact source snapshot; no source version
was reconstructed or substituted later.

The audit assigns runs by literal TARGET, avoiding a Copy/CopyCore filename
prefix collision. One intermediate audit rejected a newly arriving Factors
v2 manifest before its receipt was refreshed; the final complete snapshot
passes. This metadata arrival race is not a compiler or provenance mismatch.

Exact target source/olean/log hashes, named declarations, literal commands
and checked import closures are in [denominator-evidence.json](denominator-evidence.json).
The last dependent preflight contains 773 entries, excluding that target's
subsequent output; all ten new green outputs are retained for the next
754+20-artifact baseline.

## Independent arithmetic and scope

The final metadata-only checks are:

```
python3 docs/research/v8-no-work-100-20260907/experiments/audit_denominator_evidence.py --check-recorded
python3 docs/research/v8-no-work-100-20260907/experiments/denominator_ledger.py --check-recorded
```

The independent check reconstructs the unchanged local ceiling and verifies
`(2*117077+1)*114687 = 26854534485`, the 111-member family /
`111*28 = 3108` sparse-gamma cap, and the selected-copy caps
`100*16*136 = 217600` and `100*(2*136-1) = 27100`.
The latter uses the strict Wronskian degree bound.

The double-OOD count, sparse-gamma hit count and copy-pair count remain
conditional class arithmetic. The OOD sampler/source/Fiat-Shamir law is
uninstantiated; the sparse-branch property itself is not asserted rare;
the copy count retains source helper/pole conditions and early family
membership. The all-linear obstruction supersedes the monic-only one,
rather than being added to it. No family multiplier is put on a query tail,
and no new class bound is added to a global extraction allowance.

Read-only review confirms that the message family depends on the fixed
parent, not the actual later gamma/final. The selected bridge proves literal
message equality using encoder injectivity. It does not establish component
own-support, pre-lambda C1 descent, an efficient extractor, checked-payment
validation, actual authentication/replay or a Fiat-Shamir theorem. Higher-Y
factors remain explicit.

There is no protocol/message/verifier change, no new CU/prover measurement
and no grinding credit. NUC Lean timings are proof-check costs, not prover
benchmarks. Full-view privacy and global extraction remain separate.
