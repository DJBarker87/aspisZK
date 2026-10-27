# V374 v2 preregistration — D289, L3 preparation

Preparation only. No qualifying timing samples, no statistical leakage result,
no quiet-window marker written. V374 remains OPEN/P; target not yet established.
The lead schedules the window. This supersedes the old `generate()`/artifact-B
plan on research. It does not replace the complete-prover or same-public valid
witness obligations with kernel diagnostics.

## Frozen artifacts and attribution

Candidate source: `73070ddd512bc4e79edfc0db714fb64dc74e87b8` (rebased client
proof-account route, op223 and consolidated siblings). Harness source starts
at `c57f4eac02`; final tools-only preparation changes are in this branch's next
commit. `dudect/source-manifest.json` pins every transferred input. No files in
crates/, programs/ or scripts/ change. Ruling (l) isolation is checked in
`dudect/metadata/release-dependency-isolation.json`, including the default
programs/r1-cost-probe ELF's dependencies: neither standalone harness crate is
in the root workspace or reachable from any program dependency. No release
ELF rebuild is required by a tools-only addition.

Host: `/home/dombarker/project-offloads/codex-pv-dudect-20261027/`.
Binaries retained under `bin/`, never committed:

* Harness SHA256 `ede68055604cce057f3d0b96fa575b06f30290bba4bcdb50493b7b81a797eb02`.
* Candidate devnet_spend SHA256 `161abfd8d155a2ccf35a461cd8e03fbf909e0f8b1c59efdddec1d76e74811472`.

Both use rustc 1.94.1, LLVM 21.1.8, x86_64-unknown-linux-gnu, opt-level 3,
`RUSTFLAGS='-C link-arg=-Wl,--threads=4'`, offline, -j4. Candidate command:

```
cargo build --manifest-path tools/r1-cost-probe/Cargo.toml --release --offline --locked -j 4 --features r1p-check,aspis-r1-cost-probe/ct-host-prover --bin devnet_spend
```

Harness command replaces manifest/bin with `tools/pv-dudect/Cargo.toml` and
its only binary; its dependency features select ct-host-prover explicitly.
Lockfile and resolved feature lists are retained. This is the recommended
recipe pending owner adoption, not a newly declared release target.

Instruction binding: see `dudect/INSTRUCTION-EQUIVALENCE.md` and
`dudect/compare@5/`. Compressor (350 instructions) and QM31::try_inv (308)
match normalized standalone candidate symbols. M31::inv differs only in two
cold panic metadata references; pole scan differs only in cold bounds metadata.
SeedExpander QM31 has real return-register differences. Scalar sampling and
seed checks have different inlining/function boundaries. All experiment
intervals belong to the pinned **harness** binary; no claim that its entire
interval or whole prover equals devnet_spend is preregistered. In particular,
QM31's harness inv wrapper adds the Option check and calls M31::inv. Do not
promote a matched leaf into whole-route equivalence.

## Inputs and experiments

Class order is exactly balanced, Fisher–Yates shuffled with a public,
reproducible SplitMix64 stream seeded `0x563337342d763200`. This stream is a
synthetic test distribution, not a claim about honest entropy. Every input
is prepared before the timed interval. Fixed seeds are `[0x35;32]`; random
seeds are 32 pseudorandom bytes. Random canonical scalar operands are uniform
modulo 1..P-1 (tiny modulo bias retained, no selective retries). Random QM31
has four such independently generated limbs. Fixed scalar is 7; fixed QM31 is
(7,0,0,0). These are diagnostic secret populations, not full honest witnesses.

Every row below has **1,000,000 calls/class**, plus 10,000 balanced untimed
warm-up calls/family. CPU 2 only, single thread, monitor on CPU 0; CPU 1 is its SMT sibling and
must remain idle. Preparation snapshot: powersave governor, turbo enabled,
SMT enabled. These policies stay unchanged; dynamic frequency remains a noise
source. Public
geometry, buffer addresses by allocation policy, arity, tag, lambda, hash,
nonce/context and variant never depend on class. Allocation addresses are
not promised identical across successive calls; allocation is identical in
policy and independent of class and excluded from the interval.

| Experiment | Class 0 / class 1 secret | Fixed public inputs and interval | Dry cycles/call (0 / 1), **not a measurement** | Expected sampling time including I/O budget |
|---|---|---|---|---|
| mask-m31 | fixed / random seed | fresh actual SeedExpander, counter 0, word 8; one m31 including SHA refill/rejection | 452 / 474 | ≤5 s |
| mask-qm31 | fixed / random seed | same setup; one qm31 with four scalar rejections | 480 / 476 | ≤5 s |
| mask-m31-reject | fixed canonical internal block / random internal block with first word P | synthetic word=0, counter=0, same hash; 0 versus exactly 1 rejection, one m31 | 76 / 78 | ≤5 s |
| mask-qm31-reject | same synthetic secret block classes | same public state; 0 versus 1 rejection then four accepted limbs, one qm31 | 100 / 114 | ≤5 s |
| pole | fixed / random nonzero QM31 repeated over slots | 1024 rows ×2 sides ×2 slots; masks all 0xffff, chi=1; all_slots_clear | 10090 / 10103 | ≤50 s |
| m31-inv | fixed 7 / random nonzero canonical M31 | M31::inv, zero excluded (panics) | 386 / 392 | ≤5 s |
| qm31-inv | fixed (7,0,0,0) / random nonzero QM31 | QM31::inv including CM31/M31 norm path; zero excluded | 489 / 479 | ≤5 s |
| compress | sixteen fixed 7 limbs / sixteen random canonical limbs | tag=73, lambda=(3,5,7,11), arity=16; actual prover_shared compressor | 881 / 963 | ≤5 s |
| seed-field | fixed / random 32-byte private seed | actual entropy_nonzero32 predicate, fixed nonzero public nonce outside interval | 67 / 66 | ≤5 s |
| seed-salt | fixed / random 32-byte private seed | same actual predicate as second seed check | 66 / 71 | ≤5 s |
| seed-field-zero | zero / random private seed | synthetic API-failure diagnostic, same predicate | 66 / 65 | ≤5 s |
| seed-salt-zero | zero / random private seed | same diagnostic for salt role | 66 / 66 | ≤5 s |

The rejection diagnostics fix word position and vary the PRIVATE block only;
class 1's first 32-bit word is P, remaining words are masked below 2^30. They
are not honest-law samples. Pole arrays repeat one secret across slots and
are not claimed attainable honest witness tuples. Seed roles deliberately
measure the same original helper independently: no OS fill, full retry loop,
short-circuit composition, or joint seed-law claim. Field/salt zero cases are
not pooled with valid seeds. Status/false/true counts are retained for all.
No account key, wallet, devnet transaction or nonce-store reservation is used.

## Statistics frozen before the window

Record raw class/cycles/start-AUX/end-AUX/valid/outcome CSVs, exclusive-create,
for every call; never silently overwrite. Do not drop outliers. Start/end AUX
mismatch is the sole class-blind invalidation and causes an abort after the
current family; retain all raw rows and invalid counts. Do not replace samples
or rerun a family in the same window after an abort. Other host aborts keep
all completed/partial data; no result from an incomplete budget is a pass.

For each family, freeze cropping thresholds from its first 20,000 pooled valid
observations; exclude these calibration rows from statistical tests. For 100
crops, use dudect's percentile grid
`p_i = 1 - 0.5^(10*(i+1)/100)`, i=0..99, with cutoff at sorted pooled
`floor(p_i * 20000)` (clamped). Both classes retain strictly `cycles < cutoff`.
Also report the uncropped test. No class-specific quantile or variance filter.
`tools/pv-dudect/analyze.py` implements first-order Welch t and centered-square
Welch t (center fixed to the pooled calibration mean), counts, means and sample
variances for every cutoff. Report the whole grid with |t|>4.5 as a diagnostic
trigger, including all families/orders; no best-crop selection, optional
stopping or early clean-pass claim. Analyze once at the preregistered end.

One million/class gives approximately 990k/class held-out uncropped samples;
|t|=4.5 corresponds to a standardized mean gap about 0.0064 (about 0.0076
for ~80% normal-approximation power). Cropping reduces retained counts and
power; report them, including degenerate variance tests. This finite budget
cannot guarantee detection of arbitrary leakage. A crossing requires lead
investigation; no crossing means only no difference detected for this artifact,
input distribution, environment and budget.

## Window, command and aborts

Request **one 15-minute quiet window** from the lead: 2 minutes admission and
configuration; up to 10 minutes sampling/flushing (expected sum ≤105 seconds
plus monitor/setup); 3 minutes drain and receipt verification. Dry elapsed
family costs scaled ×1000 sum to ~16.3 seconds without CSV I/O. The per-family
budgets above deliberately allow allocation/I/O/monitor overhead. No build or
analysis is performed in the window. Offline Python analysis runs afterwards
in its own capped scope. No timing sample has been taken by this preparation.

Exact future command, on the host after the lead creates an active marker
covering at least 900 seconds, from the pinned source checkout:

```
cd /home/dombarker/project-offloads/codex-pv-dudect-20261027/src
python3 tools/pv-dudect/window.py --execute-lead-window
```

This reads `ready.json`, verifies both retained executable hashes, runs the
read-only reservation barrier and launches one scope with MemoryHigh=6G,
MemoryMax=8G, MemorySwapMax=0, TasksMax=64. The documented QUIET_WINDOW_OWNER=1
exemption is used only after the lead's marker is verified; this is not a
reservation bypass. The command never creates, edits or removes the marker.
Native command inside that scope is exactly
`taskset -c 2 .../bin/pv-dudect --measure 1000000`. All preparation scopes were
sequential and admitted. The lead's other workers must remain stopped for the
window. No Lean or Kani is involved.

Capture CPU model/microcode, kernel, governor, turbo policy, SMT topology,
frequency/temperature snapshot, ASLR, toolchain/features, limits and artifact
hashes at admission. Preparation metadata is retained separately; it is not
proof of future quietness. Abort before sampling on changed identity/CPU policy,
missing configuration, inadequate window/disk space, competing workload,
failed admission or unavailable RDTSCP/invariant TSC. Abort during sampling on
any other populated capped user build scope, an uncapped compiler/prover in
the monitored process list, memory high/max/OOM event, temperature ≥90 C,
governor/turbo/SMT/topology policy change, CPU migration, marker change, sampler
unexpected error, or sample deadline (10 minutes, also 60 seconds before window
expiry). Never extend the window, reduce counts, suppress failures, modify
MSRs/firmware, or run an opportunistic off-window measurement. Unexpected
sampler errors are visible in status counts and invalidate the run even if
the monitor did not catch them immediately. Retain abort receipts and ask the
lead for a new schedule only after investigating the cause.

**DOITM OFF (V371)** is a substantive retained limitation under Secure Boot
lockdown. This experiment cannot establish architectural data-independent
latency. V374 remains OPEN/P pending qualified data and review; V371 and every
other independent endpoint/deployment premise remain retained. No T item,
formal axiom, simulator weakening or observer weakening is added.
