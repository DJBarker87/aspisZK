# Quadratic source bridge: checked three-leaf checkpoint

Research parent: `2c63df5aab97b826d652b2536fa269bc250386d3`.
Executed runner/overlay parent: `289d7356c78a4cd493fe61a54f9548f2a0c11298`.
Borrowed V7 source: `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.

The source-bridge checkpoint contains three green leaves and 19 standard-only
axiom audits. Five attempts are retained: three green and two failed. This
does not complete the full soundness, probability, extraction or privacy task.

| Leaf / green attempt | Audits | Wall (s) | Peak RSS (KiB) |
| --- | ---: | ---: | ---: |
| QuadraticFactorSource v1 | 6 | 3.39 | 6,844,804 |
| QuadraticConstantParity v2 | 10 | 4.09 | 6,836,944 |
| QuadraticSourceDichotomy v2 | 3 | 3.19 | 6,843,192 |

All green runs exited 0 with zero swaps. ConstantParity v1 failed after
3.67 seconds / 6,803,152 KiB, and SourceDichotomy v1 failed after 3.13 seconds /
6,808,512 KiB; both had zero swaps. Their exact source snapshots, complete
logs and import manifests are retained without crediting partial axiom output.
The focused reports document the symbolic/coercion fixes; no resource cap was
raised. The receipt maps 57 exact artifact versions with no unmapped bytes.

## Inherited and new provenance

The original seven-leaf checkpoint and the twelve-leaf extension checkpoint
are immutable. Their source, output and recorded metadata hashes are verified
against their committed receipts, with the twelve extension source blobs
checked against `2c63df5a`. Their 33 and 42 recorded audits are inherited,
not recounted as new work or replayed. No old proof suite or Rust control
was run by this metadata audit.

The existing `/home/dombarker/project-offloads/aspis-higher-y.fMoMeX`
overlay/runner is reused. Its historical manifests and logs correctly retain
the older `289d7356` pin; it is not rewritten to claim the new research parent.
The initial 397 source/397 output baseline, exact pinned-main fallbacks and
native Lean 4.32.0/mathlib revisions are retained. Native packages remain a
declared pinned-revision cache boundary, not compiler reproduction.

Each new green run checks the literal command, actual before/after import
manifest, exact transitive research/V7 source-and-olean bytes, immutable
attempt source snapshot, current source/output pair and requested axiom
declarations. All five retained attempts additionally have checked GNU time
terminal/resource records and actual cgroup settings: MemoryHigh 8 GiB,
MemoryMax 10 GiB, MemorySwapMax 0, CPUQuota 200%, Lean `-j1 -M9500`.
Attempted target versions map to immutable `-source.txt` files rather than
mutable draft pathnames.

All remote traffic uses `dombarker@100.108.41.90` over Tailscale with
`BatchMode=yes`, `ConnectTimeout=10`, `StrictHostKeyChecking=yes` and
`HostKeyAlias=nuc.local`. The alias is solely for pinned-key verification.
Unrelated NUC jobs, services, VMs and concurrent main edits are untouched.
This auditor performs no remote calls or compiler runs.

## Read-only verification and scope

From the research directory:

```sh
python3 experiments/quadratic-source-bridge-audit.py --prepare-receipt
python3 experiments/quadratic-source-bridge-audit.py --check-recorded
```

The receipt generator rejects unmapped artifacts. The final check requires
all three current leaves green, all discovered attempts for these targets
retained, and an exact match with `quadratic-source-bridge-evidence.json`.
Its completion status is checkpoint-only; `full_soundness_task_complete`
remains false and global error/allowance fields remain null.

The actual mathematical statements and their remaining conditions are in
`quadratic-factor-source-review.md`, `quadratic-constant-parity-review.md`,
and `quadratic-source-dichotomy-review.md`. Deterministic source bridges do
not by themselves supply the conditional sequential sampler law, cover
all higher-Y degrees, or produce a checked bounded-resource payment witness.
Fiat–Shamir, authentication, full-view privacy and resource bounds remain
separate obligations.
