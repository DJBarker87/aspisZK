# D325 merged candidate integration gates

Source `03905a52594fadc50a1c00ab3f240a79632e8ffd`; branch `codex/pv-integ4-20261027`. No implementation source edits. Target not yet established.

Resumed under the lead elapsed-time ruling; stage 3 and the 1,000-pair differential PASS; full cost projection complete. Timing gate was expressly excluded from execution by the task. All native builds use serial capped scopes (6G/8G, swap0, TasksMax64), optimized -j4; preflight and in-scope admission require allowed:true and exit0. IDs39500–39599 reserved but no Lean compilation planned. Kani0.

## Stage 1: verifier ELFs — PASS

Fresh candidate rebuilds match all three requested SHA256 pins; see `elf-summary.json` and per-build receipts. Default 1,563,728 bytes,54.250s,684,548KiB RSS; devnet 1,563,728 bytes,35.294s,685,392KiB; Pool605,704 bytes,47.509s,677,856KiB. All exit0/swap0. The initial default launch failed before compilation on a non-executable job-local diagnostic wrapper; mode corrected, distinct retry receipt retained. No pin mismatch. `source-identity.json` verifies every exported input (7,290 files) against exact git source bytes.


|ELF|SHA256|
|---|---|
|default|`f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4`|
|devnet|`63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`|
|pool|`121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`|

## Stage 2: pinned client and route — PASS

**recipe features pending owner approval; toolchain pinned 1.94.1**

Client SHA256 `3a1b03d0eb2bbffb59631631d065d7a0dda2a57e5ca3e36d782abe49540b2ffa`,2,852,008 bytes. Exact command from `source/tools/r1-cost-probe`: `cargo build --release --offline --locked -j 4 --features r1p-check,aspis-r1-cost-probe/ct-host-prover --bin devnet_spend`. `build-client/rustc-vV.txt` records rustc1.94.1(e408947bfd200af42db322daf0fadfe7e26d3bd1),LLVM21.1.8,x86_64-unknown-linux-gnu. Compile exit0,111.512s,644,252KiB RSS,swap0. Named toolchain auto-installed before compilation.

`client-route-summary.json` and `binary-route/route-symbols.json` retain resolved direct/GOT paths from main to generate_for_mask_nonce and to op223, batch1 helper_sum/powers, batch2 sampler/weights, and batch3 public/terminal/multilinear/copy/forest symbols. prover.rs:349 and sim.rs:341 retain batch1 prover_powers. ct_pole is inlined; its selected callsite is source-pinned, not claimed as a standalone symbol. Simulator callsites are source-inspected rather than reachable from this client main. Full disassembly remains host-side with its hash; selected disassembly and relocation evidence are committed. Static route association is not a universal source/model proof.

## Stage 3: fixed-coin fixture gate — PASS (lead ruling on resume)

Candidate fixed coin0/count1 completed (exit0,29.430s,653,212KiB RSS,swap0); tx1/tx2 both pass. Exact37e5e133f8 control outputs were reused read-only from D298, whose7,013-file source identity and binary pin are retained in inherited evidence. `fixture-control-pins.json` validates the control proof/public/raw-result/ledger hashes against that committed evidence before comparison. No unchanged successful control generation was repeated. Candidate harness build exit0,40.212s,566,980KiB RSS,swap0.

Proof/public/ledger bytes and deterministic canonical result records match for both fixtures. **Raw result.json bytes differ in seconds only.** The original task explicitly requested byte-identical result records; an asynchronous clarification about the inherited seconds exception received no reply before comparison, so the literal criterion was used. No comparator exclusion was silently adopted. This is a diagnostic elapsed-time disagreement, not a proof-byte or functional-result counterexample. No source or records were repaired. The resume ruling confirms elapsed seconds are wall-clock measurements excluded by D298: proofs, public bytes, ledger bytes and canonical result records (every field except elapsed seconds) are identical, so both fixtures PASS. The original comparator exit2 and raw-byte difference remain preserved.

|Fixture|Control seconds|Candidate seconds|Proof SHA256|
|---|---:|---:|---|
|transfer|16.438374673|14.525315178|`2417323b8b8f2b0d1cb1e6e11ee691c312d76465f589dc9222e04ec34747ad3a`|
|withdrawal|15.284889236|14.864940146|`3b217e7b8ef188435d5763dd63d2e3f33889965df92b2d69a6338eb9ca4a6d44`|

`fixture-comparison.json` retains every raw/deterministic hash,size,record and ledger file hash; comparison exits2. These uncoordinated single samples are not the quiet-window timing gate and establish no timing pass.

## Stage 4: 1,000-pair whole-prover differential — PASS

Fresh coins6000–6999 against shipped `c57a344726745387efb38d1571d885c69ce829ee`, candidate runtime source `03905a52594fadc50a1c00ab3f240a79632e8ffd`. The inherited command in TIMING-PLAN.md completed exit0,12,610.878s,620,468KiB peak process RSS,6,444,756,992-byte cgroup peak,swap0. Caps6G/8G/swap0/TasksMax64; maximum3 prover processes. Resource final: no OOM or task-limit events. Twenty-one ten-minute resource reviews record continuing completed cases under the original cap.

All1,000 pairs passed:600 complete proof pairs,100 rejected-prefix pairs (within600),400 matched error-result pairs,4 complete oracle-log pairs(6006,6007,6010,6011). Public/proof/oracle bytes and deterministic records match. `combined/record-ledger-audit.json` additionally confirms1,000 canonical record and ledger pairs; all1,000 raw result records are byte-identical too. The differential harness emits no elapsed field. The harness and comparator are byte-identical between revisions. Both exported source sets match git (6,521/7,290 files); build/toolchain/binary/runner pins, comparisons, records, logs and resource receipts are retained under `combined/`.

No case was rerun. A separate post-run audit failed before reading the corpus because its script upload had been refused (exit78, overlooked when a following progress command returned0). The cooldown elapsed while the admitted differential continued; a fresh upload admission succeeded, supplying the missing inputs before the distinct successful audit. Failed/refused receipts remain in `audit-corpus-scope-001/`, `upload-final-tools/`; successful receipts are `audit-corpus-inputs-present-002/`, `upload-final-tools-retry/`. This was not a differential disagreement or a repeated differential cohort.

## Stage 5: full cumulative cost projection — COMPLETE; quiet timing unrun

`cost-projection.json` and `tools/pv-integ4-20261027/project-cost.py` add the recorded op223 whole-prover median differences to the observed-call projections for batches1–3. Op223's exact receipt is `evidence/pv-quiet-20261027/comparison.json` (D286 gate, lead D289 acceptance), with scope receipt `measurement-scope/receipt/receipt.json` in that packet. Ratios are0.9995449685449413 /1.0006407030160893; measured median deltas are−0.006545295s /+0.009123198s. `OP223-COST.md` retains control/candidate pins and medians. No new op223 whole-prover timing ran.

Batch1 was measured in a job-private scratch package, with no implementation committed under crates/. Original helper_sum/powers remain the frozen public functions; original pole is exact c57a344726 source. The copied functions are imported from the pinned candidate. The optimized probe uses five ordered original/copy rounds on fixed inputs (helper/pole1024 rows, powersN29), retains every sample and takes the median of the paired per-call deltas. `batch1-projection.json` and `batch1-cost-run/receipt/stdout.log` retain the data; `scratch/batch1-cost/pins.json` pins all inputs, Cargo.lock and the probe binary, with rustc1.94.1 recorded. Build/run receipts are `batch1-cost-build-001/` and `batch1-cost-run/` (exit0,38.403s /4.200s,565,248 /2,112KiB RSS,swap0).

|Op|Original median µs|Copy median µs|Median paired delta µs/call|Transfer calls|Withdrawal calls|
|---|---:|---:|---:|---:|---:|
|230|1.01413366|1.01235540|−0.00217324|2|2|
|254|1.08328650|1.09597640|+0.01348860|1|1|
|258|3.43373745|2.69876205|−0.72530138|1|1|

Paired-delta medians need not equal the difference of the two displayed marginal medians. Each coin0 fixture used one proof attempt. Counts cover the complete prover call before verification; instrumented elapsed times are not performance results. Batch1 contributes−0.71615926µs per fixture. Counter-source manifests, exact instrumented text, binary pin, output records and byte/ledger equivalence are in `batch1-counts/`. The added counter field is excluded only from the instrumentation consistency check; all original deterministic fields match. `restored.json` and `combined-candidate-post-cost-source-identity.json` confirm exact restoration of all7,290 exported source files. No instrumented source or binary is used as the candidate gate artifact.

|Fixture|Op223 Δs|Batch1 Δs|Batch2 Δs|Batch3 Δs|Cumulative Δs|Percent of14.38s|14.38s + projection|
|---|---:|---:|---:|---:|---:|---:|---:|
|transfer|−0.006545295|−0.000000716159|−0.000012496441|+0.235335884610|+0.228777377010|+1.590941426%|14.608777377010s|
|withdrawal|+0.009123198|−0.000000716159|−0.000012496441|+0.236124374960|+0.245234360360|+1.705384982%|14.625234360360s|

Batch3's final mask-expanded table already includes its predecessor groups; they are not added again. Batch2 retains its inclusive materialize/raw overlap. Inputs mix op223 coins100–104, batch1/3 coin0 and batch2 coin100. This is a finite mixed-fixture projection with microbenchmark noise, not a measured merged-candidate median, a universal/worst-case cost bound, or a timing-gate pass.

## Stage 6: timing plan, cleanup and premise accounting

**No timing gate was run.** `TIMING-PLAN.md` retains the exact future quiet command, setup, controls,5 same-coin processes per side,median<15s and<=1.10×shipped prover requirements, and quiet/admission guards. It also retains the exact not-run differential command and inherited corpus driver. Future setup and prerequisite acceptance are required; this stopped job has not installed or run the combined cohort.

`cleanup.json` records deletion of this job’s SBF/native Cargo targets and retention of all3 generated SBF keys in place at mode0600. Keys destroyed0; deployments0;transactions0;refundsN/A because keys were retained. Candidate outputs,binaries and artifacts remain host-side at `/home/dombarker/project-offloads/codex-pv-integ4-20261027/`; no binary/key/ELF/olean is committed. Root checkout,other worktrees,and shared sources/objects untouched.

Only job-private evidence and runner files changed. No implementation or Lean source changed. No Lean module needed recompiling:0/20 attempts,IDs39500–39599 entirely unused;Kani0/0. `scope-and-premises.json` records before/after obligations:removed0,added0,weakened0,changed0;T stays exactly entropy_law,entropy_kernel,observation. Runtime checks do not remove source/executable adequacy,E1/E2,real RunJoin,OS failure independence,inversion boundary,client proof-account adoption,L1/L2/L3 or coherent endpoint/deployment replay/axioms obligations. No simulator or observer was weakened. **Target not yet established.**

Stop reason: raw result record bytes disagree in elapsed seconds only under the literal task criterion. Next deliverable: lead resolution of that criterion, then the fresh1,000-pair differential againstc57a344726; supply missing op223/batch1 cost tables for a full projection; quiet timing remains a separate lead-coordinated gate. No push.

`COMMIT-LOG.txt` records stage commits before the final handoff commit. `validation.json` records receipt/limit/source checks and the runner syntax check.
