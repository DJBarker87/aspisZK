# D298 combined next-cycle plan — NOT EXECUTED

This plan gates **op223 + route (ii) batch 1 (230/254/258) + records**.
Candidate: `9ff5a4594ec1cad5b5d12c7cb5a49270f9b098e3` (implementation frozen).
Control: `c57a344726745387efb38d1571d885c69ce829ee`.
Template: `evidence/pv-op223-20261027/TIMING-PLAN.md`.
The lead must freeze a new revision and repeat affected prerequisite gates if records or any covered source changes. These commands are a plan, not execution receipts.

Require all three ELF pins, fixed-coin deterministic fixture bytes and records,
route symbols, and the relevant Lean source/axiom audit before differential execution.
Recommended recipe pending owner approval; toolchain unpinned. Record host rustc
1.94.1 `-Vv`, both Cargo.lock files, source identities and binary SHA256/size.

## Prepare and build (future cycle only)

```sh
export HOST=dombarker@100.108.41.90
export D=/home/dombarker/project-offloads/codex-pv-integ1-20261027/d298
export NEXT_REV=9ff5a4594ec1cad5b5d12c7cb5a49270f9b098e3
ssh "$HOST" "mkdir -p $D/combined/baseline/source $D/combined/candidate/source"
for side in baseline candidate; do
  rev=c57a344726745387efb38d1571d885c69ce829ee
  test "$side" = baseline || rev="$NEXT_REV"
  git archive "$rev" Cargo.toml Cargo.lock .cargo crates programs audit xtask tools \
    docs/research/v8-r0-zk-20261009/refine \
    docs/research/v8-r0-zk-20261009/c3 \
    docs/research/v8-r0-zk-20261009/z4 |
    ssh "$HOST" "tar xf - -C $D/combined/$side/source"
  git rev-parse "$rev" | ssh "$HOST" "cat > $D/combined/$side/source-revision.txt"
done
python3 tools/pv-integ3-20261027/prepare_combined_runners.py "$NEXT_REV"
for side in baseline candidate; do
  ssh "$HOST" "python3 $D/combined/$side/native.py $side build-fixture cargo build --release --offline --locked -j 4 -p aspis-r1-cost-probe --example prover_rw_gate --features optimized-terminal,r1p-check,ct-host-prover"
  ssh "$HOST" "python3 $D/combined/$side/native.py $side build-differential cargo build --release --offline --locked -j 4 -p aspis-r1-cost-probe --example prover_rw_differential --features optimized-terminal,r1p-check,ct-host-prover"
done
```

Run and retain the shared reservation receipt before each upload as well as
before each scope: admission requires **allowed:true AND exit0**. Retain runner
hashes; runners refuse existing output paths. Builds are serial and expected
to spend time in optimized compilation; differential/timing time is expected
in complete retry-owner proof generation and P_R1 elimination. One scope,
MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64; never raise caps.

## 1,000-pair whole-prover differential

```sh
ssh "$HOST" "python3 $D/combined/run_host.py combined-differential-001 '[\"python3\", \"$D/combined/corpus.py\"]'"
```

Use unchanged whole-prover harness and comparator, matched fresh coins
6000–6999: 1,000 pairs, 600 complete proof pairs, 100 rejected-prefix pairs,
400 error observations and four complete oracle-log pairs (6006,6007,6010,6011).
Require exact public/proof bytes, result observations, durable records and
complete emitted oracle streams; abort immediately on any disagreement.
Maximum three optimized prover processes total inside the single capped scope.
Any missing case, incomplete comparison, binary pin change, task-limit event
or OOM invalidates the cohort. Retain complete comparisons and resource/exit/
wall/RSS/swap/source receipts; review after ten minutes without a newly completed
case. Do not rerun an unchanged failed cohort. Hash and collect evidence before
removing raw corpus; securely retain all keys and authority-bearing records.

## Lead-coordinated quiet timing, after differential PASS

```sh
ssh "$HOST" "python3 $D/combined/run_host.py combined-quiet-001 '[\"python3\", \"$D/combined/timing.py\", \"combined-quiet-001-results\"]'"
```

The lead coordinates Stream A and the quiet-window marker. Workers never edit
or remove it or bypass reservation holds. Baseline first, then candidate; five
fresh processes each with identical coins 100–104; each generates transfer and
withdrawal. Per fixture, require candidate median **strictly <15 seconds** and
**≤1.10× control median**, using the harness's reported prover seconds. Compare
matched public/proof bytes and deterministic result/ledger records as well.
Retain every sample and full result record, before/after quiet guards, load and
scope inventories, binary hashes/sizes, commands and capped resource receipts.
A foreign populated capped scope or failed quiet guard invalidates the window;
partial samples are not qualified timing. An invalid window needs a changed,
lead-coordinated window before retrying. Reservation/quiet holds: three-minute
cooldown, fresh receipt labels, up to ten retries; no cap increase.

No differential or timing was run by D298. Target not yet established. No
endpoint premise is discharged by this plan, and T remains exactly
entropy_law, entropy_kernel, observation.
