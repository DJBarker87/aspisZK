# D298 integrated candidate gates — 2026-10-27

Branch `codex/pv-integ3-20261027`; runtime and proof source
`9ff5a4594ec1cad5b5d12c7cb5a49270f9b098e3`.
This supersedes the D282 status previously in this README; its evidence remains
unchanged beside `d298/`. No implementation or Lean source was edited.
**Target not yet established.** No privacy endpoint premise was removed.

## 1. All three verifier ELFs — PASS

Fresh rebuilds of the integrated candidate using the `0c9dc9a4cc` integration
recipe reproduce all requested pins. These are candidate rebuilds, not reused
predecessor measurements. Full command, source pin, admission, GNU time and
resource receipts are under `d298/build-*/`; `d298/elf-summary.json` indexes pins.

| ELF | SHA256 | Bytes | Exit | Wall s | Peak RSS KiB | Swap |
|---|---|---:|---:|---:|---:|---:|---:|
| default | `f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4` | 1563728 | 0 | 53.313 | 685816 | 0 |
| devnet | `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299` | 1563728 | 0 | 36.024 | 685972 | 0 |
| pool | `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548` | 605704 | 0 | 64.929 | 680280 | 0 |

All runs are serial 6G high/8G max/zero swap/64-task scopes, with both
`allowed:true` and exit0 required for admission and an in-scope barrier.
One Pool reservation refusal consumed a three-minute cooldown. Its next
admitted launch failed before project compilation on rustc helper-thread
`WouldBlock`; the changed retry restricted CPU affinity to 0–3 under unchanged
caps and -j4. Failed and refused receipts are retained. No ELF mismatch occurred.
SBF stack diagnostics remain in the logs; the outputs are byte-identical to pins.

## 2. Recommended devnet_spend build and route — PASS

**recommended recipe pending owner approval; toolchain unpinned**

Client SHA256 `8a929b74d3246b71f05b631b7a386b22f179bf7ccafb254be21766c6edf86207`; 2746024 bytes.
Host compiler is rustc 1.94.1 (e408947bf, 2026-03-25); `-Vv` is retained.

```sh
cargo build --manifest-path tools/r1-cost-probe/Cargo.toml --release --offline --locked -j 4 --features r1p-check,aspis-r1-cost-probe/ct-host-prover --bin devnet_spend
```

Compilation used taskset CPU0–3 and the same capped scope; runtime fixture
executions use the normal CPU set. `d298/client-summary.json`, command,
binary pins and resource receipt identify the actual build. `d298/binary-route/`
contains selected disassembly, resolved direct/GOT call paths, symbols and
relocation/disassembly hashes. Starting from `devnet_spend::main`, the actual
optimized ELF reaches `generate_for_mask_nonce` and
`prover_shared::compress_tagged_tuple`; `op223-site.json` pins the op223
source call and PC path. No reachable generic96 route was found by the
resolved-edge traversal. This is static route evidence, not executable/model
adequacy or an endpoint privacy proof.

## 3. Fixed-coin fixture bytes — PASS for established deterministic records

Freshly built both exact revisions: control `37e5e133f8` and candidate
`9ff5a4594e`. Exported inputs match git byte-for-byte (7,013 control and
7,037 candidate files; both `*-source-identity.json`). Both optimized runs
generate transfer0 and withdrawal0 using coin0, count1.

| Fixture | Public bytes | Proof bytes | Ledger records | Deterministic result |
|---|---|---|---|---|
| transfer | identical | identical | identical | identical |
| withdrawal | identical | identical | identical | identical |

**Literal raw result.json bytes differ in diagnostic elapsed `seconds` only.**
The established D282/batch1 comparator excludes that one field and compares
canonical serialized records; every other result field and every ledger file
is byte-identical. Raw hashes, sizes, complete records and exact differing
fields are retained in `d298/fixture-comparison.json`; no raw JSON equality
is claimed. This interpretation was disclosed during execution. Both verifier
stages succeed. No proof/public/durable record disagreement occurred.
These are two deterministic fixture pairs, not the 1,000-pair differential.

## 4. Lean import-change check — no recompilation required

Changed imported sources, listed before any potential compile: **none**.
`d298/lean-source-assessment.json` records 217 resolved source rows.
The op223 closure matches the already integrated/audited `0c9dc9a4cc` files;
all 82 batch1 modules match batch1 head `c9abf274fa`. The stronger whole-tree
check finds no modified/deleted existing Lean file from either predecessor.
Added modules do not change the resolved imports. Ruling(h') source authority
remains the env-J rebuild/rebuild2 records; no shared source/object was written.

Per the task's conditional rule, **0/30 Lean attempts, 0 Kani**. IDs
**28000–28099 all unused**. This is reuse of unchanged focused proof evidence,
not a new compile or coherent deployment-closure replay.

Reused successful receipt/axiom evidence:

- `53906.json` / `53907.json` beside this README: `PV_Op223_Source.op223_source`
  and `PV_Op223_V164.refinement` on the preceding integrated closure.
- `evidence/pv-batch1-20261027/lean-receipts/53701/receipt.json`:
  source laws and equality theorems for op230,254,258, plus shifts/row laws.
- Batch1 `53702` typed audit and `53703` frozen-manifest audit; all 82 final
  source hashes are covered in its `FINAL-AUDIT.json`.

Their accepted axiom lists are subsets of propext,Classical.choice,Quot.sound.
The old receipts retain exact target, source/dependency hashes, exit, wall,
RSS, swap and full printed axiom output. No forbidden primitive was added.

## 5. Combined next-cycle plan — NOT RUN

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
  ssh "$HOST" "python3 /home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy/reservation.py $D/combined/upload-$side.json > $D/combined/upload-$side.log 2>&1 && python3 -c 'import json; assert json.load(open(\"$D/combined/upload-$side.json\"))[\"allowed\"]'" || exit $?
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

## Cleanup, premise accounting and handoff

`d298/cleanup.json` records deletion of all four D298 cargo targets and secure
retention of 3 generated SBF keys at mode0600.
No key was destroyed; no deployment, transaction, authority change or refund
was performed. Fixtures, binaries and evidence remain in the job-owned host
directory `/home/dombarker/project-offloads/codex-pv-integ1-20261027/d298/`.
The earlier host run and all shared env-J sources/objects are untouched.

`d298/PROCESS.md` records launch failures and a procedural deviation: the
initial upload lacked a separate pre-scp reservation receipt, although both
admission gates preceded compilation. Later uploads have dedicated receipts.

Before/after endpoint and deployment premises are unchanged: removed0,added0,
weakened0. T remains exactly entropy_law,entropy_kernel,observation. These
integration measurements retain source/executable adequacy, E1/E2, actual
RunJoin, entropy/kernel bridge, witness-independent native OS failure, client
proof-account adoption, inversion boundary, L1/L2/L3, and endpoint/deployment
closure obligations. No fact was folded into T or simulator/observer weakened.

Next deliverable: execute the combined 1,000-pair differential on the frozen
candidate, then the lead-coordinated quiet-window timing gate. Neither ran
here. No release/adoption or privacy target claim is made. No push.
