# Worst-case CU upper bound, second method (2026-10-19)

Pre-registration followed: `design/PREREG-CU-UPPER-BOUND-2-20261019.md`
(target, method steps 1-7, PASS/FAIL/INCOMPLETE, labels). Criteria unchanged.
This is a second method; the first method's FAIL
(`design/LEAD-REVIEW-CU-BOUND-20261019.md`) stands as recorded.

Labels: **[measured]** = LiteSVM replay CU of one concrete accepted
transaction; **[analytical]** = derived from source/ELF, traced per-site counts
and the Agave 4.2.1 cost schedule; **[swept]** = maximum over the step-7 sweep.

## Verdict

**PASS** as pre-registered, as an argument with executable checks, not a
formal proof (section 7 lists what it rests on).

| | Transfer | Withdrawal |
|---|---:|---:|
| B_stage1 [analytical] (max over 2 stage-1 variants) | **1,283,656** | **1,282,782** |
| B_settlement [analytical] (max over 12 settlement variants) | **1,199,817** | **1,212,803** |
| Worst measured variant, stage 1 [measured] | 1,239,122 (split 11) | 1,237,750 (split 11) |
| Worst measured variant, settlement [measured] | 1,165,208 (split 10, rollover, prefunded marker) | 1,174,590 (same) |
| Swept maximum, stage 1 [swept] | 1,239,160 | 1,237,750 |
| Swept maximum, settlement [swept] | 1,165,208 | 1,174,664 |

Both bounds are at most 1,300,000 for each kind; steps 1-7 are complete; no
site is unclassified (`analysis/residuals.json`: `unclassified: []`); 886
accepted runs of the sweep sets (443 per kind) are all below their variant's
B (`bound.json` `sweep.violations: []`). The stage-1 margin is 16.3k
(transfer) and 17.2k (withdrawal); the settlement margin is 100k and 87k.

Dominant terms of the tightest bound (stage 1, split 11, transfer): measured
1,239,122, plus value-dependent branches (R1) 24,631, never-taken arms counted
at full cost (R3) 11,371, the query-scan source site 5,320, loops entered only
through counted arms 2,439, loop trip caps 716 and loop exits 57. The largest
single R3 sites are the five further query-scan blocks (4,690,
`r0_transcript.rs:312`) and the circle-sample fallback (3,964,
`sampler.rs:122`). For the settlement (withdrawal, split 10, rollover,
prefunded): measured 1,174,590, nested-verifier R1 19,539, Pool trip caps
8,414 (CPI account loops and the 32-byte seed check at their caps), Pool R3
6,303.

## 0. Target pin and controls

Source: `research` at cf1828114 (this job's base), shipped to the build host
as a `git archive` of the Rust workspace, `tools/r1-cost-probe` and the
`docs/research/v8-r0-zk-20261009/{refine,z4,c3}` crates the workspace and the
optional `r1p-check` dependency name. Toolchain: `cargo-build-sbf` 3.1.13,
platform-tools v1.52, LiteSVM 0.16.0 with Agave 4.2.1 (as every prior R1 CU
receipt). Hashes and sizes: `artifacts-sha256.txt`; no ELF or binary is
committed.

| Artifact | Features | SHA-256 | Relation to earlier pins |
|---|---|---|---|
| verifier (deployed) | `pool-adapter,private-leaf-salts` | `4421aafd...6bb9291` (1,406,768 B) | `.text` and `.rodata` byte-identical to `a70f30bd...`; 39 bytes differ, all in `.data.rel.ro` at a 24-byte stride, each +7: panic `Location` line numbers shifted by the 7 lines added to `verifier.rs`'s `Error` enum (cfg(`prover`) variants, ad57ac42f) |
| verifier (linked) | same | `f2a8303f...81a2e01` | audit input; `.text` equals the deployed `.text` |
| verifier `cu-profiling` | `+cu-profiling` | `b93577f5...0602e6` | step 6 only |
| Pool (deployed) | `r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit` | `121f3e29...2581548` (605,704 B) | identical to the Pool B1 ELF (`LEAD-REVIEW-POOL-B1-20261019.md`) |
| Pool (linked) | same | `9121c1fc...45a4cf` | identical to B1 linked |
| registry | pinned, not rebuilt | `7ad46f0d...67d01ab` | as both earlier jobs |

The only source changes between the first method's base (bee5825f0) and this
base that reach these two ELFs are the B1/B4 Pool changes (`programs/aspis-pool`)
and the host-only `prover`/`r1p-check` additions in `aspis-r1-cost-probe`; the
latter change no verifier instruction (`.text` identical). The Pool source at
the base is identical to the B1 worker commit 48a8bd8a1 (`git diff` empty for
`programs`, `crates/aspis-core`, `crates/aspis-statement`, `tools`).

Driver: the Pool B1 measurement driver (`pool_gate.rs` sha256 `747cf4df...`,
derived by `pool-b1-20261019/harness/patch_driver_b1.py measure` from the
first method's sweep driver `d4b6a555...`), compiled against the base tree:
`pool_gate` `a8e94825...` and the `litesvm/register-tracing` variant
`ac7ded38...`. Its options used here: `--pairs`, `--seed`, `--split`,
`--uniform-lane`, `--zeroed-genesis-page`, `--prefund-marker`, `--reuse`.
Both native builds aborted once in `rust-lld` with EAGAIN (thread creation
under `TasksMax=64`: lld starts one thread per core, 22 here) and were rebuilt
with `RUSTFLAGS=-C link-arg=-Wl,--threads=4`; the first Pool SBF build aborted
the same way in a build-script link and the unchanged rebuild passed
(`receipts/builds/{native-driver,native-driver-trace,sbf-pool}`).

A line-tables-only build of each program (`*-debuglines`, `harness/build-sbf.sh`
with `DEBUGLINES=1`) is used only to name source lines for ELF slots. Its
`.text` is not byte-identical (verifier 0xa8 bytes shorter), so a line is
attached to a slot only inside functions whose instruction bytes match
between the two builds apart from call offsets (section 2).

**Controls [measured].** The six saved fixtures
(`aspis-r1-rollover-measurement-20261019/fixtures/{transfer,withdrawal}-{13,255,1023}`)
replayed with the rebuilt ELFs and driver reproduce the Pool B1 figures exactly:

| Fixture | Stage 1 | Nested stage 2 | Settlement | History |
|---|---:|---:|---:|---|
| transfer-13 | 1,199,648 | 1,034,767 | 1,129,757 | same-page |
| transfer-255 | 1,199,567 | 1,034,718 | 1,161,066 | rollover |
| transfer-1023 | 1,199,687 | 1,034,688 | 1,160,974 | rollover |
| withdrawal-13 | 1,198,225 | 1,034,510 | 1,138,950 | same-page |
| withdrawal-255 | 1,198,264 | 1,034,675 | 1,170,523 | rollover |
| withdrawal-1023 | 1,198,386 | 1,034,477 | 1,170,263 | rollover |

(`runs/control/sweep.jsonl`.)

## 1. Variants measured (step 1)

Every admitted discrete variant was measured directly (`harness/make_plans2.py`,
plans `variants` and `variants-extra`; 264 accepted runs, each with a fresh
OS-masked proof and a seeded random witness): kind (transfer, withdrawal) x
stage-1 split ([3,10], [3,11]) x history mode (genesis = position 0 with a
zeroed page; same-page; rollover) x marker (fresh; prefunded with 1 lamport,
which takes the transfer + allocate + assign path, the costliest prefunded
path). Positions: 0 and 2^20-1 (prereg); the first method's most expensive
traced positions (stage 1: 256, 0, 4095, 1023, 255, 777777, 2^20-1;
settlement: 0, 256, 31337, 13, 255); and bit-pattern and page-fill extremes
(1, 1022, 4094, 65534, 2^19, 0x55555, 0xAAAAA, 2^20-2 same-page; 255, 511,
1023, 4095, 65535, 0x555FF, 0xAAAFF, 524287, 2^20-1 rollover). Two
witnesses per point, four per genesis group. Summary: `variants.json`.

Stage-1 variants (the stage-1 transaction does not read the history page or
the marker, so its variants are kind x split; positions enter only through
lane-position loops):

| Kind | Split | Runs | Worst [measured] | at pairs | Min [measured] | ELF residual [analytical] | Source residual [analytical] | B |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| transfer | 10 | 66 | 1,200,071 | 699135 | 1,198,566 | 38,493 | 5,320 | **1,243,884** |
| transfer | 11 | 66 | 1,239,122 | 1023 | 1,237,542 | 39,214 | 5,320 | **1,283,656** |
| withdrawal | 10 | 66 | 1,198,688 | 65535 | 1,197,058 | 39,002 | 5,320 | **1,243,010** |
| withdrawal | 11 | 66 | 1,237,750 | 13 | 1,236,114 | 39,712 | 5,320 | **1,282,782** |

Settlement variants (B = worst measured settlement + nested-verifier residual
+ Pool residual; "Pool-only" is settlement minus nested stage 2):

| Kind | Split | Mode | Prefunded | Runs | Worst [measured] | at pairs | Pool-only range [measured] | Stage-2 residual | Pool residual | B |
|---|---|---|---|---:|---:|---:|---:|---:|---:|---:|
| transfer | 10 | genesis | no | 4 | 1,132,777 | 0 | 97,681-97,681 | 21,384 | 11,001 | **1,165,162** |
| transfer | 10 | genesis | yes | 4 | 1,136,715 | 0 | 101,778-101,778 | 21,538 | 12,657 | **1,170,910** |
| transfer | 10 | rollover | no | 18 | 1,161,075 | 255 | 125,586-126,348 | 21,649 | 11,333 | **1,194,057** |
| transfer | 10 | rollover | yes | 6 | 1,165,208 | 255 | 129,683-130,445 | 21,620 | 12,989 | **1,199,817** |
| transfer | 10 | same-page | no | 26 | 1,132,299 | 0 | 56,230-97,328 | 21,401 | 21,482 | **1,175,182** |
| transfer | 10 | same-page | yes | 8 | 1,136,407 | 0 | 60,327-101,425 | 21,391 | 23,138 | **1,180,936** |
| transfer | 11 | genesis | no | 4 | 1,092,565 | 0 | 97,681-97,681 | 20,794 | 11,001 | **1,124,360** |
| transfer | 11 | genesis | yes | 4 | 1,096,754 | 0 | 101,778-101,778 | 20,703 | 12,657 | **1,130,114** |
| transfer | 11 | rollover | no | 18 | 1,120,982 | 255 | 125,586-126,348 | 20,947 | 11,333 | **1,153,262** |
| transfer | 11 | rollover | yes | 6 | 1,125,120 | 255 | 129,683-130,445 | 20,907 | 12,989 | **1,159,016** |
| transfer | 11 | same-page | no | 26 | 1,092,207 | 0 | 56,230-97,328 | 20,694 | 21,482 | **1,134,383** |
| transfer | 11 | same-page | yes | 8 | 1,096,258 | 0 | 60,327-101,425 | 20,741 | 23,138 | **1,140,137** |
| withdrawal | 10 | genesis | no | 4 | 1,142,150 | 0 | 107,131-107,131 | 21,445 | 14,502 | **1,178,097** |
| withdrawal | 10 | genesis | yes | 4 | 1,146,179 | 0 | 111,228-111,228 | 21,510 | 16,158 | **1,183,847** |
| withdrawal | 10 | rollover | no | 18 | 1,170,616 | 255 | 135,086-135,848 | 21,600 | 14,834 | **1,207,050** |
| withdrawal | 10 | rollover | yes | 6 | 1,174,590 | 255 | 139,183-139,945 | 21,723 | 16,490 | **1,212,803** |
| withdrawal | 10 | same-page | no | 26 | 1,141,723 | 0 | 65,680-106,778 | 21,415 | 24,983 | **1,188,121** |
| withdrawal | 10 | same-page | yes | 8 | 1,146,013 | 0 | 69,777-110,875 | 21,221 | 26,639 | **1,193,873** |
| withdrawal | 11 | genesis | no | 4 | 1,102,005 | 0 | 107,131-107,131 | 20,787 | 14,502 | **1,137,294** |
| withdrawal | 11 | genesis | yes | 4 | 1,106,060 | 0 | 111,228-111,228 | 20,829 | 16,158 | **1,143,047** |
| withdrawal | 11 | rollover | no | 18 | 1,130,338 | 255 | 135,086-135,848 | 21,073 | 14,834 | **1,166,245** |
| withdrawal | 11 | rollover | yes | 6 | 1,134,456 | 255 | 139,183-139,945 | 21,054 | 16,490 | **1,172,000** |
| withdrawal | 11 | same-page | no | 26 | 1,101,515 | 0 | 65,680-106,778 | 20,820 | 24,983 | **1,147,318** |
| withdrawal | 11 | same-page | yes | 8 | 1,105,789 | 0 | 69,777-110,875 | 20,642 | 26,639 | **1,153,070** |

What the measurements show [measured]: no single variant comes near 1.3M; the
worst stage-1 point is split 11 (+39.5k over split 10, as in the first
method); position changes stage 1 by at most 1.6k. The Pool cost is
seed-independent at a fixed position (B1) but depends on the position through
the history page: in same-page mode the full validation of the current page
(`history.rs:159-166`: decode the `filled` roots, then scan the unused tail
for zeros byte by byte) costs least at fill 255 and most at fill 1
(56,230 vs 97,328 Pool-only), so the same-page worst is at position 0 mod 256;
rollover scans the zeroed 8,256-byte next page and is the costliest mode
(125,586-126,348, worst at position 255 where the next index has 19 zero
bits); a prefunded marker adds 4,097 (two extra System CPIs).

## 2. Sites re-derived and classified (steps 2, 3, 5)

**Traces [measured].** 96 of the step-1 runs (per settlement variant the run
with the largest settlement CU, plus runs at the lowest and highest positions
and the largest stage 1; every settlement variant has 4-6 traced runs, every
stage-1 variant 24) were replayed with the `litesvm/register-tracing` driver
on their own proof and public input (`--reuse` of the run's sidecars,
`harness/make_trace_plan.py`). Traced CU equals measured CU for all 96
(stage 1, settlement and nested stage 2). Each run yields one stage-1
verifier trace, one nested stage-2 verifier trace and one Pool trace
(`harness/run_audit.sh`).

**ELF analysis** (`harness/sbf_slack2.py`, reusing the first method's ELF and
post-dominator code in `harness/sbf_slack.py` unchanged). For every function
that executes, the control-flow graph of the linked ELF (`.text` identical to
the deployed ELF, checked) is built for accepted executions: a call to an
abort routine (`panicking`, `*_fail`, `unwrap_failed`, `handle_alloc_error`,
`sol_panic_`, ...) is a dead end, because such a path fails the transaction
(R4). Natural loops are found with forward dominators (no irreducible loop in
any of the three programs); each back edge is redirected to a per-loop sink, so
the graph is acyclic: a branch inside a loop body has its join inside the
iteration, and the loop itself becomes a trip-count site. On that graph,
straight-line `mov rX, K; ...; jCC rX, imm` sequences are decided statically
(jump threading on cloned nodes), which removes paths no execution can take
(materialised booleans of `||` chains). For every executed conditional
branch the immediate post-dominator and, per arm, the longest and shortest
path to it are computed; a call weighs 1 plus the callee's maximum inclusive
instruction count observed over all traces, or, for a callee never executed,
its static acyclic maximum (a looping never-executed callee needs a cited cap).
Per trace the tool records each branch's count, taken count and full decision
sequence (hash), each loop's header executions, back-edge traversals, entries
(edge counts on the CFG as compiled; header = back + entries holds for every
loop) and the largest trip count of a single entry (frame-aware second pass),
and the fewest instructions any frame executed after a branch before
returning. Syscall counts and lengths are constant within every variant (the
only differing argument is the clock-sysvar buffer pointer, which does not
change its cost).

**Coverage (step 5).** Executed conditional branches: stage-1 verifier 9,176,
nested stage-2 verifier 5,600, Pool 1,886 (all three ELFs; 16,662). Every one
is classified per variant (`sites.json`; rule legend there), and
`analysis/residuals.json` lists `unclassified: []` after the rules below.
This includes the Pool's `core::ops::FnOnce::call_once` closure that the
first method left open (it is `dispatch_pair_forest_terminal_readonly_v1` /
`invoke_pair_forest_terminal`, `pair_forest_dispatch.rs:71-412`): its arms
are classified (16 R3 counted, 2 loop-control, 2 trip-capped loops, 1 loop in
a counted arm; the rest R2/R4/positional), so none of the 69 sites is left
open. Union over variants: R1 5,481 / 3,029 / 2 (stage 1 / stage 2 / Pool),
R3 221 / 743 / 147, loop-control 251 / 155 / 117, R2 3,239 / 2,940 / 1,627,
R0 78 / 58 / 10.

**Exclusions with a code citation (step 3 and step 4).** A never-taken arm is
excluded (not counted) only by one of 28 rules, each naming the code that
makes the arm impossible in an accepted run of the variant
(`harness/make_rules.py` / `harness/rules.json`; per site in `sites.json`
`exclusion_or_cap_citations`). Classes:
- positional Vec growth whose pushed lengths are fixed (checkpoint writer
  `verifier.rs:354-371`; `QueryGeometry::for_range` `verifier.rs:184-211`;
  R0P `public_bytes`, layout fixed per kind, `pair_forest_semantic_terminal.rs:2017-2077,
  1327-1361`; `heap::filled` `heap.rs:5-10`; the SBF entrypoint deserializer
  `solana-program-entrypoint-2.3.0 lib.rs:467-480`; `bincode-1.3.3
  internal.rs:25-36`);
- route and variant constants: verifier route tag (`r1_pool_adapter.rs:1019-1025`),
  Pool magic dispatch (`processor.rs:2425-2470`), proof variant S2 (the adapter
  passes exactly `proof_bytes(S2)` bytes and `parse_shape` checks the length,
  `r1_pool_adapter.rs:115-125, 295`, `verifier.rs:44-60`), transition kind
  (`pair_forest_terminal.rs:420-426, 485-492`, `pair_forest.rs:1665-1705`),
  history mode (`pair_forest.rs:1232-1244, 806-815`), prefunded marker
  (`processor.rs:409-447`), System instruction per call site
  (`processor.rs:385-449`), pending batching always `Some`
  (`verifier.rs:399, 433, 455`), S2 Weights paths including the identity
  `shared_two_point` (statement point rows 0 and 2 differ only at coordinates
  6, 7, which the d = 2, 3 factors do not read: `state_only_prefix.rs:600-614`,
  `weights.rs:120-127, 181-253`, `transport.rs:4`);
- stored-bump fast paths whose search fallback can only reject
  (`registry.rs:299-370`, `pair_forest.rs:548-583`) and hint routes that always
  pass `Some` (`pair_forest.rs:1239-1258`, `1697-1705`);
- arms that only reject (marker classification `nullifier.rs:201-206`,
  duplicate keys `processor.rs:200-209`, verifier error mapping
  `r1_pool_adapter.rs:1009`) and arithmetic impossibilities
  (`pair_forest_copy_terminal.rs:696-699`, PDA seed limits
  `solana-pubkey-2.4.0 lib.rs:912-922`).
No arms are combined by max across sites; within a site the arms are
alternatives of one branch execution, so its longest arm is its maximum.
Every other never-taken arm is counted at its longest path (R3), including the
circle-sample fallback (`sampler.rs:122`, 3,964 per stage 1) and the five
further query-scan blocks (`r0_transcript.rs:311-318`, 4,690).

**Trip caps.** A loop whose header/back-edge counts are identical in every
traced run of the variant and that no counted arm can lengthen is positional
(L0, as the first method's R0). Every other loop, and every loop reached only
through a counted arm, has a cited per-entry cap: 27 rules, e.g. 20 frontier
levels (`pair_forest.rs:606-613, 1392-1399`, `r1_pool_adapter.rs:476-483`,
`pair_tree_profile.rs:466-471`), `while carry < 20`
(`pair_forest_semantic_terminal.rs:107-118`), the 1,768-byte checkpoint zero
scan (`r1_pool_adapter.rs:940`), page slots `filled <= 256` and the unused-byte
scan per mode (`history.rs:159-166`, `pair_forest.rs:854, 1263`), the two
registry accounts (`pair_forest_dispatch.rs:135`, `pair_forest.rs:1295-1296`),
CPI account loops (at most 18 accounts, `pair_forest.rs:1306`), the 32-byte
seed (`nullifier.rs:72-93`), weights length 64 = final_len(S2)
(`transport.rs:9`). Loops whose trip count is a compile-time constant
(`four_dots`, copy-terminal tables, Weights tensors, record parsers) use the
traced maximum per entry, which is the constant.

## 3. Per-site residuals and B per variant (steps 2-4)

`harness/residual.py` computes, for each variant V and its measured worst run
w (traced), B_V = CU(w) + the sum of per-site residuals:
- branch site b (join inside the iteration or the function):
  `own(b) = taken_w*(Lmax - L_target) + (count_w - taken_w)*(Lmax - L_fallthrough)`,
  L_arm the longest path of that arm, Lmax over the arms that can execute in V
  (observed in a traced run of V, or never-taken and not excluded). A site at
  its worst in w adds 0 (prereg step 2). Nested regions lie inside the arms,
  so the sum over sites accounts for every instruction once; a branch never
  executed in V lies inside an arm whose longest path its enclosing site
  already counts. A never-taken counted arm also pays, once per execution, the
  cap of every syscall it alone reaches (Agave 4.2.1 schedule; `rules.json`
  `syscall_caps`) and the cited cap of a looping callee it calls;
- R0: both arms taken but the full decision sequence identical in every traced
  run of V (at least 3): positional, 0 (the first method's R0, also applied to
  the in-iteration choice of loop-control branches);
- loop-control branch (an arm continues the innermost enclosing loop): the
  in-iteration choice as above; exits are costed once per loop entry at the
  loop: entries_w x (longest possible exit tail - shortest observed exit tail);
- loop h with a cap N per entry: (N x entries_w - header_count_w) x W_iter(h),
  W_iter the longest single iteration; a loop entered only through a counted
  arm adds count_w x (N - 1) x W_iter.
- source site S-QSCAN-EXTRA (stage 1): the five further scan blocks are
  counted by the ELF site at the observed maximum scan() cost (931); a block
  costs at most 931 + 8 x 133 (contains loops at their caps) = 1,995, so
  5 x 1,064 = 5,320 is added [analytical].

Residuals of the bounding variants [analytical] (`bound.json`):

| Variant | measured w | R1 | R3 | loops (L1, LA) | loop-control | source | B |
|---|---:|---:|---:|---:|---:|---:|---:|
| stage 1, transfer, split 11 | 1,239,122 | 24,631 | 11,371 | 3,155 | 57 | 5,320 | **1,283,656** |
| stage 1, withdrawal, split 11 | 1,237,750 | 24,488 | 11,868 | 3,299 | 57 | 5,320 | **1,282,782** |
| settlement, transfer, 10, rollover, prefunded: stage 2 / Pool | 1,165,208 | 19,478 / 0 | 1,878 / 4,062 | 0 / 8,483 | 264 / 444 | - | **1,199,817** |
| settlement, withdrawal, 10, rollover, prefunded: stage 2 / Pool | 1,174,590 | 19,539 / 0 | 1,920 / 6,303 | 0 / 9,743 | 264 / 444 | - | **1,212,803** |

Every site with its ELF address, source lines (from the line-table build,
where the function's instructions match the measured build), class, rule per
variant, maximum residual, and, in the variant that sets B, its traced count,
cost in the worst input (longest-path weight of the taken arms), maximum cost
and residual, is in `sites.json` (9,037 sites with a residual, exclusion or cap;
7,826 further sites listed by address under R0/R2/L0/LC with residual 0).

## 4. Profile consistency (step 6)

The `cu-profiling` verifier (`b93577f5...`) replayed 24 measured runs on their
own proofs (6 per kind and split: lowest, middle and highest positions, the
worst stage 1 and the worst settlement; `harness/make_profile_plan.py`).
Per-phase CU (`analysis/profile-phases.json`, first method's
`profile_phases.py`): 196 phases vary across the runs of a (kind, split,
transaction) group, the largest being `r1:semantic` (up to 1,311),
stage-2 `r1:parsed` (673) and `r1:relation` (173). `harness/phase_attrib2.py`
maps each phase to the functions that run in it (the first method's map,
extended) and requires its range to be at most the traced spreads plus the
counted residuals of the sites in those functions: **0 of 196 phases are
unexplained**. Pool, function level: in 80 (variant, function) pairs a
function's instruction count varies between traced runs of the same
variant, and each of them contains a site or loop whose decisions vary in
that variant: **0 unexplained** (`analysis/phase-attribution.json`).

## 5. Sweep (step 7)

**Time plan (recorded before launch at 16:14 UTC, 2026-10-19).** Nothing is
compiled for the sweep: the driver, the traced driver and both ELFs are the
pinned builds of section 0. Time goes into (1) the OS-masked S2 proof that the
driver generates for every run (the dominant part) and (2) two LiteSVM
transactions (stage 1, settlement with its nested stage 2). The 264 step-1
variant runs measured 4.47-4.72 s wall each (mean 4.55 s, peak RSS 259 MiB,
0 swaps; `receipts/run-ledger-variants.jsonl`), so 600 random runs
(300 per kind) take about 46 min sequentially in one capped scope, plus the
targeted runs (about 5 min). No down-sampling is needed. The traced replays
for the per-site analysis (section 2) are separate (96 runs, 20 GB of register
traces, deleted after analysis).

Plan (`harness/make_plans2.py`, seed 0x201610192): per kind 300 runs with a
fresh OS-masked proof and a random witness (input value, outputs, membership
path, super-root path, `selected_second`, hence nullifier, output lane and
marker address), random checkpoint sequence, position drawn 25% uniform on
[0, 2^20), 25% rollover positions 256k-1, 20% below 4096, 15% within 1024 of
2^20-1, 15% from {0, 1, 255, 256, 1023, 2^19, 2^20-1}; split 10 or 11 with
equal probability; at position 0 a zeroed genesis page with probability 1/2;
a prefunded marker address (1, 890,880 or 10^9 lamports) with probability
0.15.

**Results [swept].** 600 random runs (300 per kind) and 16 targeted runs
(positions 127 and 2^20-129, the largest same-page trailing-ones count, 7;
rollover markers prefunded with 890,880 and with 10^9 lamports), all accepted (`sweep.jsonl`, sets `random`, `targeted`). Random set:
split 10/11 285/315; same-page 410, rollover 182, genesis 8; prefunded markers
106. Together
with the 264 variant runs and the 6 controls, 886 accepted runs (443 per kind)
are checked against their variant's B: **no value exceeds it**.

| Kind | Split | Random runs | Stage 1 min-max | Settlement min-max |
|---|---|---:|---:|---:|
| transfer | 10 | 135 | 1,198,371-1,199,937 | 1,093,372-1,164,819 |
| transfer | 11 | 165 | 1,238,503-1,239,160 | 1,051,432-1,125,221 |
| withdrawal | 10 | 150 | 1,196,961-1,198,635 | 1,100,263-1,174,125 |
| withdrawal | 11 | 150 | 1,236,220-1,237,724 | 1,061,323-1,134,217 |

Swept maxima over all sets: stage 1 1,239,160 (transfer) /
1,237,750 (withdrawal); settlement
1,165,208 / 1,174,664.
The withdrawal settlement maximum (1,174,664, the targeted rollover run whose
marker holds 890,880 lamports, the rent-exempt minimum of an empty account,
so the transfer CPI still runs) is 74 CU above the worst step-1 point of its
variant (1,174,590, which the bound starts from); its B is 1,212,803. Targeted inputs
exist only for controllable sites (kind, split, mode, marker, position bits,
page fill); the transcript-driven sites (value branches, circle fallback,
duplicate query draws) cannot be steered without breaking Fiat-Shamir and are
covered by the residuals, not by targeted runs. Random sweep wall time
0.80 h in one capped scope, peak RSS 258 MiB, 0 swaps.

## 6. Receipts

All work ran on the build host (NUC) under `systemd-run --user --scope -p
MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64`, `-j 4`,
optimized builds; host work dir
`/home/dombarker/project-offloads/codex-r1-cu-bound2-20261019`.
- Builds (`receipts/builds/*/receipt.json`: command, exit, wall, peak RSS,
  swaps, cgroup caps): SBF verifier, verifier `cu-profiling`, Pool, and their
  line-table builds, 35-40 s each, peak RSS <= 0.79 GB; native drivers 76 s
  and 84 s, peak 0.64 GB. Failed first attempts are kept (`native-driver`,
  `native-driver-trace`, `sbf-pool`: rust-lld EAGAIN under TasksMax, see
  section 0). 0 swaps everywhere.
- Runs (`receipts/run-ledger.jsonl`, one line per run with command, exit,
  wall, RSS, swaps, cgroup): 6 controls, 264 variants, 96 traced replays,
  24 profiled replays, 16 targeted, 600 random; 0 failures, wall 4.5 s per run,
  peak RSS 258 MiB, 0 swaps.
- Analyses (`receipts/builds/audit-main-1` ... `audit-main-10`,
  `residual-final`): ten successive versions of `sbf_slack2.py` over the same
  96 traces, each a tool change (abort dead ends, jump threading, loop
  handling, entry counting, per-entry trips), not a rerun; peak RSS 1.38 GB.
  The 20 GB of register traces were deleted after the last analysis.
- Source revision cf1828114 (this job's base); no Lean compilation, so
  `#print axioms` is N/A. No ELF, `.so`, binary or archive is committed
  (`artifacts-sha256.txt` has SHA-256 and sizes).

## 7. What the bound rests on (labels)

[analytical] B is an argument with executable checks, as pre-registered, not
a formal proof. It rests on:
1. **Callee weights.** A call inside an arm weighs the callee's maximum
   inclusive instruction count observed over all traces (or its static
   maximum if never executed). Variation inside a callee on the measured
   path is counted by the callee's own sites; for a call that only a counted
   never-taken arm makes, a callee path costlier than any observed invocation
   is not separately bounded (the first method made the same assumption).
2. **Positional sites (R0, L0).** A branch or loop whose decisions are
   identical in all traced runs of a variant (4-26 runs with different
   witnesses, masks and positions) is taken as fixed by the code, as in the
   first method. Rare data-dependent events of this kind are listed as sites
   instead: query-scan duplicates (S-QSCAN-EXTRA plus the counted extra
   blocks) and the circle fallback.
3. **Exclusions and caps.** 28 exclusions, 27 trip caps and 2 callee caps, each with the
   code citation in `rules.json`; eight caps use the traced maximum per entry:
   seven for loops whose trip count is a compile-time constant, one
   (`contains` in the query scan) because every accepted run passes through
   every accepted_len value 0..21.
4. **Syscalls.** Counts and lengths are constant within each variant in every
   trace; syscalls reachable only on a counted arm are charged at their
   schedule cap.
5. **Scope.** Rejected transactions are out of scope; the bound covers the
   pinned ELFs (`4421aafd...`, `121f3e29...`), Agave 4.2.1 costs and the
   transaction shapes of the driver (prefunded markers with 1, 890,880 and
   10^9 lamports measured; a prefund changes only the System CPI sequence).
[measured] values are LiteSVM replays; [swept] values are the 886 accepted
runs of section 5.
