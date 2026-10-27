# D325 quiet-window command — NOT RUN

Candidate runtime source `03905a52594fadc50a1c00ab3f240a79632e8ffd`.
Shipped control `c57a344726745387efb38d1571d885c69ce829ee`.
This plan requires fixture acceptance and a passing fresh 1,000-pair differential first.
It conveys no timing approval and no performance result.

Use the existing integ3 setup from `evidence/pv-integ1-20261027/README.md`, with
D=/home/dombarker/project-offloads/codex-pv-integ4-20261027 and NEXT_REV set to
the full candidate above. Archive each revision into D/combined/{baseline,candidate}/source;
never alter the candidate tree or shared sources. Record pre-upload reservation receipts,
source identities, both Cargo.lock hashes, runner hashes, rustc -vV and binary hashes/sizes.
The unchanged whole-prover harness is `prover_rw_gate`; build each side serially:

```sh
cargo build --release --offline --locked -j 4 -p aspis-r1-cost-probe --example prover_rw_gate --features optimized-terminal,r1p-check,ct-host-prover
```

Use the inherited combined native/capped/admission runners rebased into D/combined
(their source-revision.txt must pin each side separately). `combined-timing.py` in this
job's tools is the inherited timing driver with only the job path changed; install it
as D/combined/timing.py. Install the unchanged op223 quiet-preflight.py and the inherited
run_host.py/capped.py with D pointing at D/combined. This setup has not launched timing.
The exact command after those preparations, prerequisite PASS, and a lead-coordinated
quiet window is:

```sh
ssh dombarker@100.108.41.90 "python3 /home/dombarker/project-offloads/codex-pv-integ4-20261027/combined/run_host.py combined-quiet-001 '[\"python3\",\"/home/dombarker/project-offloads/codex-pv-integ4-20261027/combined/timing.py\",\"combined-quiet-001-results\"]'"
```

Baseline first, then candidate; five fresh processes per side, matching coins100–104;
each process proves transfer and withdrawal. For each fixture require candidate median
strictly <15s and <=1.10× shipped-control median. Retain all samples, complete result
records, public/proof bytes and durable ledger comparisons, before/after quiet guards,
load/scope inventory and binary pins. The established comparator excludes diagnostic
seconds only from deterministic records; any literal-result requirement must be resolved
before running this plan.

One scope only: MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64. Admission requires
allowed:true AND exit0 both before and inside scope. Never bypass holds or edit/remove
the quiet marker. A foreign populated capped scope or failed quiet guard invalidates
the window; partial samples are not qualified timing. Changed lead-coordinated window
required before any retry. Retain keys securely and delete only rebuildable targets.

Differential command before timing, after preparing the same two pinned sources and
building `prover_rw_differential` with the same feature set and locked release recipe:

```sh
ssh dombarker@100.108.41.90 "python3 /home/dombarker/project-offloads/codex-pv-integ4-20261027/combined/run_host.py combined-differential-001 '[\"python3\",\"/home/dombarker/project-offloads/codex-pv-integ4-20261027/combined/corpus.py\"]'"
```

Install this job's `combined-corpus.py` as corpus.py: inherited coins6000–6999,
1,000 pairs,600 complete proof pairs,100 rejected-prefix pairs,400 error observations,
4 complete oracle-log pairs(6006,6007,6010,6011),maximum3 prover processes inside
one capped scope. Stop on first discrepancy; task-limit/OOM events invalidate the cohort.
Time is expected in complete retry-owner proof generation and P_R1 elimination;
review after10min without a completed case. No differential or timing result is claimed
by this plan. Target not yet established.
