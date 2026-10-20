# Adopted-build CU bound (2026-10-20)

Target: e90cf2f800f7177e5cca47aa7e5ba59a940130dd.
Branch: codex/cx-cu-bound3-20261020.
Criteria: PREREG-CU-UPPER-BOUND-2-20261019 steps 1–7, unchanged.
Labels: measured LiteSVM CU; analytical residual bounds; swept accepted runs.

## Verdict: INCOMPLETE under the literal requested checklist

**All computed inequalities pass** for the adopted build's nonempty accepted
variants. No executed site is unclassified; every new-format loop has a
code-cited cap. There are zero unexplained phase/function variations and
zero sweep violations. These are arguments with executable checks, not
formal proofs.

| Kind | B stage 1 [analytical] | B settlement [analytical] | Stage-1 headroom | Settlement headroom |
|---|---:|---:|---:|---:|
| transfer | **1,292,965** | **1,265,783** | 7,035 | 34,217 |
| withdrawal | **1,292,314** | **1,278,858** | 7,686 | 21,142 |

The requested accepted coverage of **both** splits cannot be completed:
split 11 has an empty accepted domain in the adopted build. The source
rejects it and both executable counterexamples reject with Parse /
InvalidInstructionData. There is no accepted worst input from which to
compute a second-method B for split 11 (`variants.json`: B=null, excluded).
No criterion is waived or silently replaced by split-10 coverage. Thus this
report does **not** issue a full steps-1–7 PASS despite all numeric bounds
being below 1,300,000. This is a coverage obstruction, not an exceeded bound;
the preregistration's site-incompleteness condition is separately empty.

## Scope obstruction

Adopted source fixes SPLIT = 10 and rejects split 11 (candidate.rs parse_shape/tx1; adapter retains [3,11] route). The requested two accepted splits cannot both be swept. Test rejection separately; never count it as accepted coverage. Bit-reversed query sets are component targets, not Fiat-Shamir-forced accepted whole transactions.

## Runs

Host work directory /home/dombarker/project-offloads/codex-cx-cu-bound3-20261020. Own capped scopes: MemoryHigh 6G, MemoryMax 8G, MemorySwapMax 0, TasksMax 64; optimized cargo -j 4; linker threads 4. No Lean work. No key cleanup.

## Target pin and controls (step 0)

Rebuilt from e90cf2f80 in the assigned host tree. Deployed verifier SHA-256
`8cf8d84ed0fe340a190b4f40a9f953f0e0523370299ba3ec8bbed9d65b88ace3`
(1,405,680 bytes), linked
`f313df1045a12626f41fc84950a872a4c7565a38c9a3df853590e605b3de7f66`;
Pool `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`
(605,704 bytes), linked `9121c1fc52a3b7f17146e57102979985ce37af1866407234dcfd3e37cd45a4cf`.
Both whole deployed and linked files equal the adopted pins. Registry remains
`7ad46f0d4b102a7c9699149d23bf6e065b6151feeaca95977d0a3146167d01ab`.

Six saved adopted-fixture controls reproduce exactly (stage 1 / settlement):
transfer-13 1,196,046 / 1,135,481; transfer-255 1,198,152 / 1,166,524;
transfer-1023 1,192,314 / 1,166,269; withdrawal-13 1,192,444 / 1,145,777;
withdrawal-255 1,192,575 / 1,175,735; withdrawal-1023 1,194,056 / 1,173,313.
Fresh proofs in the grid use OS masks and seeded witnesses; old secret mask
entropy is not reconstructed. The adopted measurement driver is rebuilt
against this base; tracing is its identical source plus litesvm/register-tracing.

Failed build attempts are retained: omitted workspace manifests (metadata
failure); then `-Wl,--threads=4` passed to the direct SBF rust-lld, which
rejects cc's `-Wl` wrapper. Corrected configuration uses native target flags
`-C link-arg=-Wl,--threads=4` and SBF target flags `-C link-arg=--threads=4`.
No memory-pressure failure or cap increase occurred.

## Component checks

`harness/component_checks.rs` calls the actual public wrapper of
state_only_prefix.rs:600-614 on 4,096 QM31 point inputs, including all-zero,
all-one, all-(p-1) and xorshift-generated limbs. Row 0 equals z; row 2
is z except for complementing coordinates 6 and 7; coordinates 5,4,9,8
read by X-WEIGHTS-S2 agree. Executable result: PASS. This supports the
source argument; it is not exhaustive over the extension field.

Bit-reversed indices attain supplied-node counts 146 (10,18), 128 (10,16),
172 (12,18), 150 (12,16), giving six-slot total
2*(146+172)+128+150=914. Each of these four component multiproofs is
constructed and verified by the adopted multiproof implementation; each
wrong-sibling mutation rejects. These component targets do not force an
accepted complete Fiat–Shamir transaction to use the chosen query set.

## New-format accounting

The old rule set is reused as the second-method rule set, with verifier
addresses moved only through same-named, same-size functions with equal
instructions after masking layout-dependent call and lddw operands. Pool
addresses remain exact because both Pool files are identical. Mixed-program
address rules are separated by program; unmapped stage-1 body addresses are
not guessed. `rule-address-mapping.json` records every attempted mapping.
Historical source citations retain their original cf1828114 revision;
new-format rules cite the adopted source at this job's target.

`harness/adopted_rules.py` adds code-cited limits for all new parser,
compact-decoder and multiproof loops. The binary arity is a route constant;
three trees are processed; each tree has 18 levels. Batches contain 10/12
queries; dedup only reduces distinct leaves. Sorted binary parent groups
have at most two children. Insertion-sort indices strictly decrease. A
folded-index duplicate run has at most four distinct-query preimages under
u/4. Padding scans are bounded by the six slot capacities
[146,146,128,172,172,150] (914 nodes total). Compact expansion always visits
27 fixed-shape records, expanding 426 semantic values plus 29 y1 values;
the canonical opening scan always visits 22 openings with four subslots.
Source basis for the node count: `evidence/proof-size-20261019/REPORT.md` §1.

SBF instruction residuals exclude runtime syscall charges. Unlike the old
format, binary parent-hash counts vary by query set. For each tree, parent
hashes = supplied nodes + distinct leaves - 1, so the stage maxima are
420+30-3=447 and 494+36-3=527. Agave 4.2.1 charges a SHA call on slices
[1,32,32] exactly 85+max(10,1/2)+16+16 = 127 CU. A separate source site adds
127*(parent_max-parent_count_in_the_same_measured_worst_input).
`harness/hash_residual.py` also checks that subtracting these parent calls
leaves a constant non-parent SHA-call count per kind and transaction role.
No measured maxima from the retired verifier are substituted for this work.

## Measurement grid and coverage (steps 1–6)

124 main-grid plus eight extra-genesis accepted runs cover each nonempty
accepted variant: kind x split 10 x history mode (genesis, same-page,
rollover) x fresh/prefunded marker. Endpoints 0 and 2^20-1, old expensive
positions, page-fill/trailing-bit extremes and rent/large prefunds are
included. `variants.json` records each grid position and each B. Fresh
witnesses are seeded; masks and leaf secrets use OS entropy.

70 exact-input register replays (64 selected grid/random targets, six saved
controls) have identical stage-1, nested-stage-2 and settlement CU to their
original measurements. Targets include batch node-count and sort-inversion
extremes and actual accepted proofs with duplicate folded indices in each
batch. The globally distinct 22-query bit-reversed component target attains
[146,146,128,172,172,150]; its split batches are verified by actual code.
No Fiat–Shamir challenge is altered to manufacture an accepted transaction.

Executed conditional branches: **9,288 stage 1, 5,677 stage 2, 1,886 Pool**,
16,851 total. All have arm bounds and per-variant classifications;
`analysis/residuals.json` has `unclassified: []`. This includes the Pool's
69 `call_once` sites inherited from the earlier review. No irreducible
function or loop-entry mismatch appears. Every executed new-format loop,
including constant decoder loops, has a cited source cap in `sites.json`.
Line mapping accepts only equal instruction bodies with layout operands
masked; unmapped functions keep their exact ELF locations.

Twelve cu-profiling replays yield **58 varying verifier phases**, all covered
by listed sites. **40 varying Pool functions** (counted per variant) are
explained. `analysis/phase-attribution.json`: both unexplained lists empty.
Subtracting binary-parent calls leaves constant non-parent SHA counts per
kind and role (`analysis/hash-residuals.json`), so parent-call variation is
explicitly charged. Profiling builds are attribution evidence, not the
release CU measurements.

Tightest stage-1 bound (transfer): measured 1,202,054 + ELF residual 85,591
+ query-scan residual 5,320 + parent-SHA residual 0 = 1,292,965. Its measured
input already reaches all 447 stage-1 binary parents. ELF residual terms:
48,245 loop trips/exits, 22,576 varying-arm residuals, 11,386 never-taken-arm
cost, 2,439 loops inside counted arms and 945 loop-control choices. Tightest
settlement (withdrawal, rollover, prefunded): 1,183,771 + 77,166 nested
verifier + 16,778 Pool + 1,143 parent SHA = 1,278,858. Dominant new costs
are the capped parent traversal and duplicate-run loops; no redesign was made.

## Assumptions and limits

The second method and the lead review's assumptions are retained: called
functions in counted arms use observed inclusive maxima where the method
allows them; positional decision classes are empirical; fixed-trip loops
may use their observed per-entry maximum only with the source constant
identified; source lines require byte-matched functions. Transcript-driven
fallbacks, duplicate draws and field-value arms use residuals rather than
changed Fiat–Shamir challenges. All new input-dependent multiproof loop
limits are source caps; none is an observed maximum substituted as a cap.

The X-WEIGHTS-S2 executable check closes the requested release follow-up.
The complete-transaction bit-reversed target is not claimed: the component
check exercises the true worst-case query geometry, and the source bound
covers all accepted challenge sets. No Lean/refinement/privacy obligation
is closed by this Rust/SBF evidence. Stage-1 headroom is only 7,035 CU;
any verifier change requires a new bound analysis.

## Receipts, failures and retained artifacts

`receipts/run-ledger.jsonl` records each command, exit, wall time, peak RSS,
swaps, cgroup limits and source revision. Build/analysis receipts additionally
record cgroup peak memory. No Lean was run (`#print axioms`: N/A).
`artifacts-sha256.txt` records SHA-256 and size instead of executable files.
Native toolchain: Rust/Cargo 1.94.1; SBF: Solana 3.1.13, platform-tools v1.52;
LiteSVM 0.16.0 / Agave 4.2.1. The exact measurement driver source and lockfile
are in `harness/driver/` (pool_gate.rs SHA 7b48182a...).

Besides the build failures above, two orchestration errors are retained:
concatenating grid and targeted trace picks initially repeated two labels;
the run stopped before a repeated execution, then resumed only missing
labels after deduplicating the plan. An inherited rules JSON was accidentally
restored by a harness sync; the analysis refused to produce B because sites
were unclassified. The corrected pipeline regenerates the address rules
before every analysis (`analysis-regenerated-rules` receipt). The earlier
failed analysis is not represented as a valid bound. Neither incident
changes a release measurement, source ELF or completed trace input.

Only this task's large `.regs` and `.insns` files are removed after hashing
and validation; `trace-inventory.json` records exact SHA-256 and bytes. Raw
CFG/trace-count JSON, proof/public sidecars, signing keys, build caches and
small trace identifiers remain on the host. No wallet key is deleted or
unlinked, and no binaries are committed. No broad unchanged runtime,
reproducible-build or formal suite is rerun; the byte-identical adopted pins
retain their existing stack/runtime evidence.

## Remaining

- Accepted split-11 coverage is impossible under the adopted source. It
  requires a lead-level interpretation or a new pre-registration for the
  now-single-split accepted domain; this job changes neither criteria nor
  verifier code.
- Bit-reversed worst geometry is executable component evidence, not a
  manufactured Fiat–Shamir complete-transaction fixture.
- The inherited second-method assumptions and all formal proof-size/privacy
  obligations remain as labelled above.

## Final sweep and per-variant B (step 7)

**752 accepted runs, 376 per kind**, including 300 random witnesses/masks
per kind, 66 grid runs per kind, four targeted runs per kind, three saved
controls and three freshly re-proved controls per kind. The six fresh
controls also match the saved public statements exactly. Positions include
0 and 1,048,575 and span the intervening range; all three history modes and
fresh/prefunded markers are exercised. All accepted runs use split 10.
Two split-11 attempts reject and are excluded from accepted counts.

| Kind | Swept max stage 1 | Swept max settlement | Violations of variant B |
|---|---:|---:|---:|
| transfer | 1,202,054 | 1,173,996 | 0 |
| withdrawal | 1,200,657 | 1,183,771 | 0 |

Settlement B by accepted variant (all split 10; analytical):

| Kind | Mode | Fresh marker | Prefunded marker |
|---|---|---:|---:|
| transfer | genesis | 1,231,194 | 1,236,837 |
| transfer | same-page | 1,241,261 | 1,246,888 |
| transfer | rollover | 1,260,120 | 1,265,783 |
| withdrawal | genesis | 1,244,072 | 1,249,893 |
| withdrawal | same-page | 1,254,277 | 1,259,787 |
| withdrawal | rollover | 1,273,116 | 1,278,858 |

Stage-1 B is 1,292,965 transfer / 1,292,314 withdrawal (kind x split only).
All bounds and each measured-worst residual decomposition are in `bound.json`.
`validation.json` verifies all 836 native execution receipts (including
traces, profiling and expected split-11 rejections): zero swaps, required
cgroup memory limits, exact trace-CU parity and every B arithmetic identity.
The largest native execution peak RSS is 286,444 KiB; the 70-input static
trace audit peaks at 1,099,248 KiB, wall 181.836 s, exit 0, swaps 0.

Cleanup removed **1,332** large trace files totaling **15,378,911,912 bytes**;
SHA/size inventory is committed. Frozen local evidence checks passed, including
752 accepted rows, 836 receipts, all B inequalities, classifications, attribution
and absence of executable/fixture binaries or key files. Python harness syntax
checks pass. `git diff --check` reports only preserved whitespace in raw failed
compiler/rejection diagnostics; those receipt bytes are intentionally retained.
