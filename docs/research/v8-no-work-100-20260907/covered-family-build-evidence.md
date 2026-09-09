# Covered-family continuation: build and evidence boundary

Parent `f19673b4fe72cf74ae687a926eeae9d1e5a6a52e`, borrowed formal source
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`. No previous source, runner or
evidence record is changed by this build setup.

## Fresh isolated NUC workspace

The workspace is `/home/dombarker/project-offloads/aspis-covered-family.rfQFkf`.
It reuses immutable hardlinks from the frozen `aspis-masked-tail.m4IQIB`
overlay and the existing pinned native Lean/Mathlib cache. The old overlay
and unrelated host services/VMs remain untouched. Only new target names may
be written in this overlay; an imported old source/output is never overwritten.

The initial host check found load average 0.01 and 46,963,818,496 available
bytes, with no active build scope. This is a point-in-time resource check,
not a continuing reservation. Root coordinates one heavy job at a time.

`bootstrap_covered_family.py` checked 344 source blobs against the new research
or borrowed revision and 344 retained compiled artifacts. It incorporates
the previous three successful `QuotientFamilyCore`, `QuotientFamilySelected`
and `EarlyC1Family` outputs, including the last output absent from that run's
preflight manifest. The prior origin is `bc23dfeb`; the older nested origin
remains recorded as `b006d34f`. Neither is presented as the new parent.

Remote metadata preflight passed all 688 artifacts and every declared native
package revision. It did not invoke Lean or rebuild a dependency. Evidence:
`experiments/covered-family-bootstrap-preflight.log`.

```
covered-family-initial-manifest.json SHA-256
aec29d19e0277209a33e245c9434527dc9bf35c594b3f40bcce589998cdcec30
run_covered_family_nuc.sh SHA-256
e73b7924f7631454e4a8b7d34b25cb2012d581435181097d003a668291c26248
```

## Focused execution

Upload a new source only after its draft is ready. Wait for the root's explicit
build-slot grant, then use a fresh run tag:

```
ssh dombarker@nuc.local 'bash /home/dombarker/project-offloads/aspis-covered-family.rfQFkf/run_covered_family_nuc.sh /home/dombarker/project-offloads/aspis-covered-family.rfQFkf TARGET fresh-tag'
```

The runner uses the previously established selected-cache profile:
MemoryHigh 8 GiB, MemoryMax 10 GiB, MemorySwapMax 0, CPUQuota 200%,
Lean `-j1 -M9500`. This is a cached single-leaf check, not a cold build.
Actual cgroup settings, command, wall/RSS/swap, terminal exit, source/output
hashes and named axiom audits are logged. Failed checks remain diagnostics;
changing a failed target requires preserving its previous source snapshot.

Each successful target becomes immutable in the task's green-output state.
Every dependent run gets a new manifest that pins those new source/output
bytes before import. Return the log, per-run manifest and compiled outputs
to the local research evidence directory. No package-wide replay is needed.

## Audit scope

The new read-only `experiments/audit_covered_family_evidence.py` has an explicit
five-leaf census: `CoveredFirstCollision`, `SelectedCoveredRelation`,
`CausalCoveredRecovery`, `SelectedWeightedCopyCore`, and
`SelectedWeightedCopyRows`. It inspects their actual imported source/output
closure and standard-axiom reports; it does not rerun the previous three
cardinality leaves or earlier ten-leaf suite. Missing or stale target evidence
remains pending and returns a nonzero exit.

`covered-family-transfer.json` maps remote artifact versions to retained
local bytes. `covered-family-evidence.json` records the resulting focused
status, rechecked using:

```
python3 docs/research/v8-no-work-100-20260907/experiments/audit_covered_family_evidence.py --check-recorded
```

Final status: all five current-source leaves are green, with thirty
standard-only axiom audits and zero swaps. The actual imported artifacts
checked for the five targets number 81, 589, 671, 1 and 3 respectively.
Twelve run logs are retained: five successful checks and seven failed
elaboration diagnostics with exact historical source snapshots. No failure
is counted as release evidence.

| Target | Green run | Wall | Peak RSS (KiB) | Audits |
| --- | --- | ---: | ---: | ---: |
| `CoveredFirstCollision` | v4 | 3.11 s | 6,712,992 | 6 |
| `SelectedCoveredRelation` | v4 | 3.68 s | 6,882,480 | 4 |
| `CausalCoveredRecovery` | v1 | 3.11 s | 6,869,984 | 8 |
| `SelectedWeightedCopyCore` | v1 | 1.38 s | 1,761,188 | 7 |
| `SelectedWeightedCopyRows` | v2 | 0.89 s | 1,734,220 | 5 |

The audit additionally checks the exact local event ledger without a new
proof replay, and compares all 64 selected mask entries and 136 public
weight/tag/level entries with the pinned Rust constants. The latter is
static metadata evidence, not the still-missing endpoint/pattern constructor
or a Rust-to-Lean execution refinement.

The audit inherits the previous source-to-olean evidence: matching cache
hashes do not constitute a fresh compiler reproduction. Native package
revisions are a declared compiler/cache boundary, not a replay of Mathlib,
machine-code verification or Fiat–Shamir source refinement.

New probability/extraction theorems, if checked, retain their own hypotheses
and event scope. Build success does not establish a complete payment witness,
authenticated replay availability, full-view privacy, global 100-bit security,
or matched complete-transaction CU parity. Proof body remains 40,282 bytes.
