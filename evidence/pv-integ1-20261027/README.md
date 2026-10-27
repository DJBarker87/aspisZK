# D282 integrated candidate gates

Branch `codex/pv-integ1-20261027`; integrated source
`0c9dc9a4cc` (full revision in `tools/pv-integ1-20261027/source-revision.txt`).
No implementation or proof source edits are authorized by this task.
Target not yet established. No privacy endpoint premise is removed by integration
measurements; all existing mathematical, deployment, E1/E2, real RunJoin,
OS-failure-independence and L1/L2/L3 obligations retain their meanings. T remains
exactly entropy_law, entropy_kernel and observation.

## Stage 1: verifier artifacts

PASS: all three rebuilt ELFs match the requested pins. See `elf-summary.json`
and the per-build comparisons/receipts. Default and devnet are 1,563,728 bytes;
Pool size is recorded in the summary. Confirmed default SHA-256
`f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4`;
devnet `63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`;
Pool `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`.
Every build runs alone in a 6G/8G/zero-swap/64-task scope after admission and
barrier checks. Expected work: optimized SBF compilation, not proof generation.
Source identity is checked byte-for-byte by `source-identity.json`.
The initial launch failed before compilation because the copied diagnostic
wrapper lacked execute permission; execute permission was restored for the new
launch. Three aggregate-reservation refusals and three-minute cooldowns preceded the
successful default build. Their admission receipts are preserved separately.

## Stage 2: client build and route

PASS. SHA-256 `5fc6c98d2e34b873faae3773064f6b0eda505623b161a703647c7787b2f46688`,
2,747,928 bytes. `route-symbols.json`, `route-disassembly.txt` and
`op223-site.json` retain resolved call paths from `devnet_spend::main` to
`generate_for_mask_nonce` and `prover_shared::compress_tagged_tuple`, plus the
source call at host_semantic.rs:423. This is binary/source route evidence, not
a whole-prover refinement theorem. Build exit 0, 126.807 seconds, peak process
RSS 636,300 KiB, swap 0; see capped receipt for aggregate peak. Two admission
refusals preceded the successful third client admission.

Label: **recommended recipe pending owner approval; toolchain unpinned**.
Recipe: host rustc 1.94.1, release, offline, locked, four build jobs:

```
cargo build --manifest-path tools/r1-cost-probe/Cargo.toml --release --offline --locked -j 4 --features r1p-check,aspis-r1-cost-probe/ct-host-prover --bin devnet_spend
```

## Stage 3: fixed-coin fixtures

PASS against `c57a344726`; transfer and withdrawal, deterministic coin 0.
`baseline-reuse.json` establishes unchanged implementation/harness/lockfile
inputs since the control artifact build. `fixture-control-pin-check.json`
checks control proof/public pins and complete control result records against
the evidence actually committed at c57. Both proof files are 57,607 bytes and
verify through tx1/tx2. See `fixture-comparison.json` and capped receipts.
All public/proof bytes, deterministic result record bytes (canonical JSON)
and durable ledger file bytes are identical. The raw measurement `result.json`
files differ **only** in elapsed `seconds`; both raw hashes, values and all
differing fields are retained. Those measurement files are not claimed to be
byte-identical. This uses the prior fixture gate definition, excluding only
elapsed-time metadata.
Proof/public bytes, every deterministic result field and durable reservation
records were compared. Runtime measurements are evidence metadata, not quiet-window timing.

## Stage 4: Lean import audit and focused re-check

`lean-import-audit.json` lists the changed/new imported source files BEFORE any
compile. This includes the canonical P6 source and ten imported files newly
present at their canonical paths. Objects are inspected read-only. No shared
env-J source is installed or overwritten. Assigned IDs 53900–54199, budget
30 Lean attempts, zero Kani. PASS: `R1Z.PV_Op223_Source.op223_source` (53906) and
`R1Z.PV_Op223_V164.refinement` (53907) type-check against the integrated-tree
source and the retained audited import objects. All five printed axiom lists
contain only `propext`, `Classical.choice`, `Quot.sound`. Exact source hashes,
dependency object hashes/fingerprints, commands, caps, exits, walls, process and
cgroup peaks, zero swaps, and axiom output are in the per-ID receipts and
`lean-summary.json`. This is a focused re-check, not a clean deployment closure
replay or a privacy endpoint claim.

Budget: **5/30 charged Lean attempts**, **0 Kani**. 53900, 53903 and 53905
failed before theorem elaboration at missing private overlay imports
(P6Bridge, Init.Prelude, Aeneas.Command respectively). These are environment
preflight failures, not theorem counterexamples. Replacements were changed
private object environments, under the original caps. IDs 53901, 53902 and
53904 were uncharged admission refusals, with three-minute cooldowns and fresh
IDs. The retained op223 cache uses directory symlinks; the initial file-only
copy missed them. `retained-prefix-overlay.json` records preserving those
links and hash-checking all 231 imported objects in the audit, excluding the
two rebuilt targets. Earlier overlay records preserve the attempted fixes.
No shared source or object was overwritten.


Changed/new imported files (listed before compiling):

- `R1Z.PV_RW_DataPartsIff` — `docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RW_DataPartsIff.lean`
- `R1Z.PV_RW_DataProduct` — `docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RW_DataProduct.lean`
- `R1Z.ProverRw19AuditCaller` — `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRw19AuditCaller.lean`
- `R1Z.ProverRw19AuditData` — `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRw19AuditData.lean`
- `R1Z.ProverRw19AuditValue` — `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRw19AuditValue.lean`
- `R1Z.ProverRw19AuditSource` — `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRw19AuditSource.lean`
- `R1Z.ProverRw19P6Caller` — `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRw19P6Caller.lean`
- `R1Z.ProverRw19P6Join` — `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRw19P6Join.lean`
- `R1Z.ProverRw19P6ContextIdentity` — `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRw19P6ContextIdentity.lean`
- `R1Z.ProverRw19CanonicalAuditRefinement` — `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRw19CanonicalAuditRefinement.lean`
- `R1Z.ProverRwP6CompressSource` — `docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwP6CompressSource.lean`

The ten additions are new canonical paths relative to the op223 branch;
the read-only object source bytes match the integrated files. P6 source bytes
also match the integrated version. Aeneas library objects are unchanged
external-toolchain inputs, recorded by object hash.


## Stage 5: combined next-cycle gates — PLAN ONLY

This is the combined **op223 + route (ii) batch 1 + records** adoption gate,
not an op223-only rerun. Use `evidence/pv-op223-20261027/TIMING-PLAN.md` as the
standing timing template. Freeze the next combined candidate's full revision
before preparation; it does not exist as an established target in this receipt.
Control is exactly `c57a344726`, not op223's pre-rebase control `258c685f50`.
Neither the 1,000-pair differential nor timing is authorized to run here.

Preparation commands for the next cycle (lead supplies `NEXT_REV`, the full
reviewed combined candidate revision; these commands were NOT executed):

```sh
export HOST=dombarker@100.108.41.90
export D=/home/dombarker/project-offloads/codex-pv-integ1-20261027
: "${NEXT_REV:?Set the reviewed combined op223 + batch-1 + records revision}"
git rev-parse --verify "${NEXT_REV}^{commit}"
ssh "$HOST" "mkdir -p $D/combined/baseline/source $D/combined/candidate/source"
```

Export the same native build inputs as this integration task, from each exact
revision (including both lockfiles); do not overlay modified harness inputs:

```sh
for side in baseline candidate; do
  rev=c57a344726
  test "$side" = baseline || rev="$NEXT_REV"
  git archive "$rev" Cargo.toml Cargo.lock .cargo crates programs audit xtask tools \
    docs/research/v8-r0-zk-20261009/refine \
    docs/research/v8-r0-zk-20261009/c3 \
    docs/research/v8-r0-zk-20261009/z4 |
    ssh "$HOST" "tar xf - -C $D/combined/$side/source"
  git rev-parse "$rev" | ssh "$HOST" "cat > $D/combined/$side/source-revision.txt"
done
```

Install the path-adapted reservation/barrier/receipt runners and planned gate
scripts with the following preparation-only command. It verifies both source
pins, refuses to overwrite an existing runner, records all runner hashes, and
does not launch a build, differential or timing:

```sh
python3 tools/pv-integ1-20261027/prepare_combined_runners.py "$NEXT_REV"
```

The baseline and candidate have separate job-owned cargo targets. No shared
source is written.

Exact build commands after installing those runner paths:

```sh
for side in baseline candidate; do
  ssh "$HOST" "python3 $D/combined/$side/native.py $side build-fixture cargo build --release --offline --locked -j 4 -p aspis-r1-cost-probe --example prover_rw_gate --features optimized-terminal,r1p-check,ct-host-prover"
  ssh "$HOST" "python3 $D/combined/$side/native.py $side build-differential cargo build --release --offline --locked -j 4 -p aspis-r1-cost-probe --example prover_rw_differential --features optimized-terminal,r1p-check,ct-host-prover"
done
```

Both builds use host rustc 1.94.1; record `rustc -Vv`, features, source hashes,
lockfiles and binary SHA-256/size before any execution. The three rebuilt ELF
pins, integrated fixed-coin fixture comparison, and relevant focused Lean
re-checks must pass first. Re-check these prerequisites on the final combined
revision if the covered sources change.

Exact 1,000-pair whole-prover differential command:

```sh
ssh "$HOST" "python3 $D/combined/run_host.py combined-differential-001 '[\"python3\", \"$D/combined/corpus.py\"]'"
```

This is the unchanged whole-prover harness/comparator with fresh coins
6000–6999 and matched coins on both sides: 1,000 pairs, 600 complete proof
pairs, 100 rejected-prefix pairs, 400 errors and four complete oracle-log pairs
(coins 6006, 6007, 6010, 6011). Require exact result observations, public/proof
bytes, durable records and complete oracle-stream equality wherever emitted.
Fail immediately on any disagreement. At most three prover processes total,
all optimized, within one 6G/8G/zero-swap/64-task scope. A task-limit event, OOM,
missing case, incomplete comparison or binary pin change invalidates the cohort.
Expected time is whole-prover proof generation and P_R1 elimination, not build
compilation. Retain the per-pair comparison records, complete result receipts,
resource reviews and SHA/size manifest before deleting only raw proof corpus.

Only after that passes, the lead coordinates a quiet window with Stream A.
The worker never edits/deletes `QUIET_WINDOW.json`. Exact timing command:

```sh
ssh "$HOST" "python3 $D/combined/run_host.py combined-quiet-001 '[\"python3\", \"$D/combined/timing.py\", \"combined-quiet-001-results\"]'"
```

Baseline first, then candidate; five fresh processes each, identical coins
100–104, transfer and withdrawal in every process. Require per-fixture candidate
median **< 15 seconds** and **≤ 1.10 × baseline median**, using reported prover
seconds. Compare matched public/proof bytes. Retain all samples and result
records, exact commands, binary pins, before/after quiet guards, host load and
scope inventories and capped receipts. Any populated foreign capped scope or
failed quiet guard invalidates the window; partial samples do not count as
qualified timing. On admission refusal wait three minutes and use a fresh
receipt label, up to ten retries; never bypass the barrier or raise caps.
No unchanged invalidated timing rerun. Retain all keys securely; remove only
this cycle's cargo targets and raw corpus after evidence collection.

## Cleanup, scope and final disposition

All three job-owned Cargo targets and the private Lean object overlay/cache
were removed after collecting receipts and object pins. `cleanup.json` retains
three SBF keypairs in their artifact directories at mode 0600 and records their
public keys. No wallet key was deleted, deployed, spent or refunded. The first
cleanup stopped on a Cargo `.fingerprint` JSON whose filename contained
`keypair`; `cleanup-preflight-failure.json` records the classification fix and
`final-cleanup.json` confirms no Cargo targets remain. No shared source/object,
root checkout, other worktree, or other job's artifact was modified.

All changes in this branch are confined to `evidence/pv-integ1-20261027/` and
`tools/pv-integ1-20261027/`. Implementation and Lean proof source bytes remain
those of `0c9dc9a4cc`. No forbidden proof primitive or new axiom was introduced.
Before and after this task, V164 still requires the reservation equation and
`P_proof_bytes`; this task removes no privacy theorem premise and adds no trust
item. Formal source-to-model, E1/E2, real RunJoin, OS-failure independence,
L1/L2/L3 and endpoint/deployment closure obligations are retained unchanged.

The successful runs and earlier setup/admission failures are all retained;
no ELF mismatch or deterministic fixture disagreement occurred. Raw timing
metadata is explicitly unequal, as explained in stage 3. The only next-cycle
work proposed here is the combined differential and lead-coordinated quiet
window above. **Neither was executed. Target not yet established.**
