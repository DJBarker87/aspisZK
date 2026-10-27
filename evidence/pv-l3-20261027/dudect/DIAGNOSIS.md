# D295 seed-path diagnosis — diagnostic, not a V374 measurement

**Diagnostic classification: harness/setup artifact supported by the requested
controls; exact prior artifact mechanism unresolved. Target not yet established.**
No quiet window was requested, created, edited, removed or used. No Lean, Kani,
shipped-source change, fix, release rebuild, transaction or key creation occurred.
V374 and V371 remain OPEN/retained; no premise was removed, added, weakened,
or moved into T. This evidence does not qualify the thermally aborted D294 data
or establish constant time for a complete prover.

## Controls — diagnostic, not a V374 measurement

| Family | Control | Raw/class | Uncropped abs(t) first / square | Max abs(t) first / square (101 tests) |
|---|---|---:|---:|---:|
| mask-m31 | fixed A / fixed B | 1,000,000 | 0.078167 / 1.107241 | 2.764836 / 2.940349 |
| mask-m31 | fixed / random, fresh buffer | 1,000,000 | 0.618173 / 0.176279 | 2.372625 / 2.545955 |
| mask-m31 | random / random | 1,000,000 | 0.703905 / 0.647744 | 1.761045 / 1.479309 |
| mask-qm31 | fixed A / fixed B | 1,000,000 | 0.506851 / 0.246797 | 1.661836 / 2.830633 |
| mask-qm31 | fixed / random, fresh buffer | 1,000,000 | 1.283324 / 1.072143 | 1.283324 / 1.072143 |
| mask-qm31 | random / random | 1,000,000 | 0.101209 / 0.580418 | 1.979032 / 1.685013 |

Every pair has exactly 1,000,000 valid observations/class, zero AUX mismatches,
and zero false outcomes. All six pairs and both classes were interleaved in
**one** Fisher–Yates shuffled schedule of 12,000,000 calls on CPU 2. They were
not six sequential experiments. Fixed A is `[0x35;32]`, fixed B `[0xa7;32]`.
Random/random cells use independent successive SplitMix64 draws by the same
code path; this is reproducible synthetic randomness, not an entropy-law claim.
All cells first generate a random record identically; constant cells are then
replaced before sampling. All records occupy the same contiguous allocation
with identical 32-byte stride. Every timed call copies its record, including
constant-derived records, into a fresh local `[u8;32]` lifetime at the common
stack site, then source-linked `prepare` copies it into a fresh actual expander.
There is no retained fixed-class seed buffer. Allocation, all random generation,
constant selection, ordering, seed copying, initialization and zeroizing drops
are outside counter intervals. Dispatch is public and before the first stamp.
The two class paths inside each pair call the same sampler instruction body.

Diagnostic changes from the frozen measurement harness are explicit: full input
pregeneration, the common fresh-buffer path, simultaneous interleaving of six
pairs/two families, and 10,000 **global** untimed warmup calls instead of the
measurement's 10,000/family. Counts, fixed A, expander initial counter=0/word=8,
HOST_HASH, sampler bodies, counter fences and single CPU are retained. These
changes isolate value populations under common preparation but do not identify
which individual old preparation effect caused D294. No original-path positive
control was rerun; collapse is not a controlled proof that buffer identity alone
caused the old signal. Noise, scheduling and thermal state can also affect the
comparison between the old and new runs.

The table gives absolute first-order and centered-square Welch statistics.
The same frozen 20,000 pooled calibration observations, pooled-mean square
center, strict common crop cutoffs and 100-percentile grid were used, plus
uncropped tests. Calibration is excluded, leaving 1,980,000 held-out rows/pair
in total; exact class/crop counts, means, variances, cutoffs, signed statistics,
raw SHA256/size/path are in `diagnosis/diagnosis-analysis/stdout.log`.
All 606 tests/order are retained, including degenerate cuts. No outlier deletion,
resampling, threshold selection or early clean-pass rule was used.

The diagnostic analyzer aggregates identical cycle values and merges weighted
Welford moments to avoid repeating 101 updates for each of 12 million rows.
Its counts/cutoffs and both orders were checked against the frozen analyzer on
a 22,000-row deterministic fixture; maximum statistic difference is recorded
in `diagnosis/analyzer-validation.json`. This validation is a formula check,
not an additional timing run. Raw CSVs remain on the host, not in git.

## Classification — diagnostic, not a V374 measurement

The fresh-buffer fixed/random signal collapses from D294 maxima
150.669662/176.948210 (M31) and 221.701656/233.473230 (QM31) to
2.372625/2.545955 and 1.283324/1.072143. Both requested negative controls stay
below 4.5 for both orders and the whole crop grid. Under the requested decision
rule, this supports **harness artifact**, with the narrower causal statement
"the D294 signal is sensitive to harness/setup; a persistent seed-value effect
was not reproduced under common preparation." It is not evidence sufficient
to name cache warmth, buffer identity, thermal interaction or branch-history
conditioning as the sole prior cause. The old finding remains retained and
non-conforming, neither a qualified leak nor silently dismissed.

The source does contain rejection-dependent control flow. For ideal uniform
hash words each draw rejects with probability 2^-31, not with appreciable
frequency at this budget: 15,000,000 random-class first-attempt word draws give
an expected 15,000,000 / 2^31 = 0.006985 rejections. Fixed A's first four masked
words are 2118520180, 1654913217, 1505627263, 1994084878; B's are 1331006965,
1846809750, 373837753, 2137947224; none equals P=2147483647. Random-class
rejection counts were not instrumented, so zero false outcomes does not imply
zero retries. The rare path is real source behavior but is unsupported as the
explanation for a broad 150–233 t crossing. No seed-value-dependent hash latency
instruction was identified by this static inspection or these controls. DOITM
remains OFF, so this is not an architectural data-independent-latency proof.

## Source and instruction trace — diagnostic, not a V374 measurement

Source byte identity was checked against the pinned transferred manifest:
`state_only_hiding.rs` SHA256
`b02e125623d5a3b8ea97c7f8bf9a3111b9cd3625abf3d7b356e4fbd15aa759e5`;
prover `lib.rs` SHA256
`9e3da13535d8b552311a82f73610634e2587a5b46984c1e68804500dc5e03667`.
These are the candidate sources at `73070ddd512bc4e79edfc0db714fb64dc74e87b8`.
Evidence/tool base is `d03e24018cac5015c4b94f296df9f0c9154c6a6a`.
The recommended devnet_spend recipe is the exact release/offline/locked
r1p-check + aspis-r1-cost-probe/ct-host-prover command in
`../dual/V374-PLAN-v2.md`; it remains a recommendation pending owner adoption.
This job did not replace that target or rebuild that binary.

Pinned binaries, independently rehashed by the static trace:

| Binary | SHA256 |
|---|---|
| Original harness | `ede68055604cce057f3d0b96fa575b06f30290bba4bcdb50493b7b81a797eb02` |
| Recommended candidate devnet_spend | `161abfd8d155a2ccf35a461cd8e03fbf909e0f8b1c59efdddec1d76e74811472` |
| New tools-only diagnostic | `132f99405b086bab25b2ea8b1e5920f6d38e13f0499ffc697e878db58e678ca7` |

Addresses below are link-time virtual addresses in those exact x86-64 ELFs;
add the process mapping load bias for runtime addresses under ASLR. This is a
static data/control-dependence trace, not a recorded processor execution trace.
Complete addressed bodies are in `diagnosis/diagnosis-trace/*-seed-path.asm`
(terminal blank lines trimmed in the committed text excerpts);
`diagnosis/seed-dependent-addresses.json` retains instruction text, compare and
branch addresses, all four QM31 lanes, and the diagnostic binary addresses too.
The list concerns the methods requested and the candidate's scalar sampler
inlined into `sample_mask_cells`; it does not claim an audit of all downstream
uses of the sampled fields throughout the prover.

Source trace:

1. `SeedExpander::new`, `state_only_hiding.rs:388–396`: copy 32 seed bytes;
   constant counter=0, block=0, cursor=8, fixed public HashFn. No seed-based
   branch or address; constructor is inlined, no standalone symbol claimed.
2. `next_word`, lines 408–416: cursor==8 chooses a refill; lines 409–412
   hash and increment counter/reset cursor. Lines 414–416 compute 4*cursor,
   advance it and load the little-endian word. Initial cursor is public; later
   cursor/refill counts become seed-dependent **only through rejection**.
3. `m31`, lines 419–428: mask the word at line 424, compare to P at line 425,
   return accepted value or increment retry at line 426, bounded by 16 attempts.
   This compare/branch is directly seed-derived. Retry exhaustion is a public
   error with seed-dependent occurrence; timing is not constant on that path.
4. `qm31`, lines 431–435: four inlined scalar loops, with early error returns.
   These add no independent value predicate; all four lane copies are listed.
5. `state_only_mask_expander_block`, lines 1616–1617: indirect call to the
   fixed public `HashFn`, with `[domain, seed, counter_le]`, lengths 39/32/8.
   Seed bytes and counter affect hash contents, not slice addresses/lengths.
6. `aspis_prover::host_hashv`, `lib.rs:82–89`, `HOST_HASH` line 91:
   `sha2` **0.10.9** `Sha256`, three updates, finalize. The 79-byte message
   always takes two SHA-256 compression blocks including padding. No Poseidon,
   S-box, secret-indexed table or variable-length encoding is in this path.

The following tables enumerate direct seed-conditioned branches and the cursor
addresses/branches transitively affected by rejection. An indirect hash call's
**target** is public; its execution count can depend on rejection. Bounds
branches are listed conservatively: valid cursor<=8 and refill establish the
indexed load is in range, so their panic arms are unreachable here. All other
loads/stores in the expander use constant offsets or fixed stack addresses;
their values, but not effective addresses, can depend on the seed. Unconditional
jumps and return/error epilogues have fixed targets; rejection selects which
of them executes, visible in the complete addressed bodies.


### harness: `pv_dudect::kernels::state_only_hiding::measure_m31`

| Operation | Addresses (compare / branch where paired) |
|---|---|
| rejection compare and branch | `0x37758` / `0x3775e`, `0x37806` / `0x3780c` |
| retry decrement and branch | `0x3780e` / `0x37811` |
| cursor compare and branch | `0x37730` / `0x37734` |
| cursor indexed load | `0x3774f`, `0x377fd` |
| cursor bounds compare and branch | `0x37745` / `0x37749` |
| hash indirect call | `0x377d1` |

### harness: `pv_dudect::kernels::state_only_hiding::measure_qm31`

| Operation | Addresses (compare / branch where paired) |
|---|---|
| rejection compare and branch | `0x378c6` / `0x378cd`, `0x3797d` / `0x37984`, `0x379c6` / `0x379cd`, `0x37a7f` / `0x37a86`, `0x37ac5` / `0x37acb`, `0x37b83` / `0x37b89`, `0x37bd5` / `0x37bdb`, `0x37c9d` / `0x37ca3` |
| retry decrement and branch | `0x37986` / `0x37989`, `0x37a88` / `0x37a8b`, `0x37b8b` / `0x37b8e`, `0x37ca5` / `0x37ca8` |
| cursor compare and branch | `0x378a0` / `0x378a4`, `0x379a0` / `0x379a4`, `0x37aa0` / `0x37aa4`, `0x37bb0` / `0x37bb4` |
| cursor indexed load | `0x378bf`, `0x37976`, `0x379bf`, `0x37a78`, `0x37abf`, `0x37b7d`, `0x37bcf`, `0x37c97` |
| cursor bounds compare and branch | `0x378b5` / `0x378b9`, `0x379b5` / `0x379b9`, `0x37ab5` / `0x37ab9`, `0x37bc5` / `0x37bc9` |
| hash indirect call | `0x37943`, `0x37a45`, `0x37b45`, `0x37c5a` |

### candidate: `aspis_prover::state_only_hiding::SeedExpander::qm31`

| Operation | Addresses (compare / branch where paired) |
|---|---|
| rejection compare and branch | `0x13b916` / `0x13b91d`, `0x13b9cd` / `0x13b9d4`, `0x13ba16` / `0x13ba1d`, `0x13bacf` / `0x13bad6`, `0x13bb15` / `0x13bb1b`, `0x13bbd3` / `0x13bbd9`, `0x13bc25` / `0x13bc2b`, `0x13bced` / `0x13bcf3` |
| retry decrement and branch | `0x13b9d6` / `0x13b9d9`, `0x13bad8` / `0x13badb`, `0x13bbdb` / `0x13bbde`, `0x13bcf5` / `0x13bcf8` |
| cursor compare and branch | `0x13b8f0` / `0x13b8f4`, `0x13b9f0` / `0x13b9f4`, `0x13baf0` / `0x13baf4`, `0x13bc00` / `0x13bc04` |
| cursor indexed load | `0x13b90f`, `0x13b9c6`, `0x13ba0f`, `0x13bac8`, `0x13bb0f`, `0x13bbcd`, `0x13bc1f`, `0x13bce7` |
| cursor bounds compare and branch | `0x13b905` / `0x13b909`, `0x13ba05` / `0x13ba09`, `0x13bb05` / `0x13bb09`, `0x13bc15` / `0x13bc19` |
| hash indirect call | `0x13b993`, `0x13ba95`, `0x13bb95`, `0x13bcaa` |

### candidate: `aspis_prover::state_only_hiding::sample_mask_cells`

| Operation | Addresses (compare / branch where paired) |
|---|---|
| rejection compare and branch | `0x13c096` / `0x13c09d` |
| retry decrement and branch | `0x13c09f` / `0x13c0a2` |
| cursor compare and branch | `0x13bfb0` / `0x13bfb4` |
| cursor indexed load | `0x13c089` |
| cursor bounds compare and branch | `0x13c07f` / `0x13c083` |
| hash indirect call | `0x13c02b` |

### Hash internals and latency — diagnostic, not a V374 measurement

| Body / relevant instruction | Original harness | Recommended devnet_spend | Dependence |
|---|---|---|---|
| `host_hashv` entry | `0x3f910` | `0x13f940` | Three public slice lengths; update/padding branches depend on lengths and fill count, not bytes |
| memcpy calls in hash update | `0x3f98f`, `0x3f9eb`, `0x3fa4f` | `0x13f9bf`, `0x13fa1b`, `0x13fa7f` | External libc; public pointers, alignment and lengths; seed is copied as data |
| memset in padding | `0x3fb5e` | `0x13fb8e` | Public padding size; value is zero |
| `sha2::sha256::compress256` entry | `0x3fc70` | `0x1be4a0` | Cached CPU feature dispatch, then software fallback or SHA-NI |
| SHA feature-storage load | `0x3fc8c` | `0x1be4bc` | Public CPU feature byte, not seed |
| SHA feature conditional branches | `0x3fc95`, `0x3fca3` | `0x1be4c5`, `0x1be4d3` | Public cached CPU capability / initialization |
| CPUID initialization function entry | `0x428a0` | `0x1c10d0` | Potentially expensive/variable latency, public feature detection; warmed before sampling |
| SHA-NI `digest_blocks` entry | `0x428f0` | `0x1c1120` | Sequential block traversal; only block-count/loop-pointer branches |
| First SHA-NI round instruction | `0x4297b` (`sha256rnds2`) | `0x1c11ab` (`sha256rnds2`) | Seed-derived operands; no data-selected branch/address |
| SHA-NI block-loop branch | `0x42c80` | `0x1c14b0` | Public end pointer and block count |

The host CPU advertises `sha_ni`, SSSE3 and SSE4.1, so the library's public
feature dispatch selects SHA-NI after initialization. This backend selection
is inferred from source/CPU features, not captured with a dynamic branch trace.
Both compiled backends were inspected and retained in the assembly evidence.
The SHA-NI backend uses `sha256rnds2`, `sha256msg1`, `sha256msg2`, SIMD adds,
fixed-lane shuffles and sequential loads. `pshufb` is a register shuffle, not
a seed-indexed memory lookup; its endian mask is public. Round constants are
RIP-relative loads with statically chosen round indices. The software fallback
is an unrolled add/xor/and/or/rotate/shift schedule with a public block loop;
no seed-indexed memory access, byte predicate, division or other identified
operand-dependent variable-latency arithmetic appears in either body.

Source references in the pinned registry are `sha2-0.10.9/src/sha256.rs`
(dispatch and compression wrapper), `sha256/x86.rs:10–24` (schedule/round
intrinsics) and `sha256/x86.rs:43` onward (fixed block loop). Source and
instruction inspection find **no additional directly seed-dependent control
or effective address inside SHA**. Data-dependent transistor activity,
frequency effects, cache/interference noise, and an undocumented operand
latency are not excluded by that statement. Loads and external libc copies
can have variable latency for public-address/cache reasons. Libc is dynamically
linked; its runtime IFUNC-selected memcpy/memset implementation was not
instruction-audited here. Their call boundaries and public arguments are
explicitly retained rather than treating them as a proved constant-time leaf.
No actual variable-latency opcode depending on seed data was identified.

## Execution and provenance — diagnostic, not a V374 measurement

Every scope was admitted with both exit 0 **and** `allowed:true`; no refusal or
retry occurred. Scopes were sequential, with MemoryHigh=6G, MemoryMax=8G,
MemorySwapMax=0, TasksMax=64. No window exemption was set. The restored-host
flag was read. Quiet-marker absence was checked before each scope and is false
again in the trace identity output. Existing other workers were not stopped;
noise was expected. A read-only post-control CPU package snapshot was 101 C;
there is no per-call thermal/frequency series and no thermal qualification.
These ordinary off-window diagnostics do not use the V374 thermal/window
acceptance rules and do not claim to pass them.

| Sequential target | Exit | Wall seconds | Process peak RSS KiB | Cgroup peak bytes | Swap peak bytes |
|---|---:|---:|---:|---:|---:|
| Optimized diagnostic build | 0 | 23.516137 | 566524 | 882053120 | 0 |
| 12-million-call interleaved controls | 0 | 3.305504 | 470624 | 735358976 | 0 |
| Offline diagnostic analysis | 0 | 29.219630 | 56716 | 55275520 | 0 |
| Static addressed trace / binary identities | 0 | 0.844260 | 71500 | 71618560 | 0 |

Process RSS and cgroup peak are distinct metrics, not interchangeable. Exact
commands, limits, source revision, exit and timings are in `diagnosis/*receipt.json`
and the analysis/trace subdirectories; `/usr/bin/time -v` logs retain process
RSS and swaps. `#print axioms` is **N/A: no Lean** for all targets. Build time
was optimized compilation/linking against the retained cached workspace;
control time was expander calls/CSV I/O; analysis was offline statistics.
Earlier ad hoc static inspection used read-only objdump and CPU/registry reads,
without executing kernels; the final capped trace supplies the formal identity
and resource receipt. It was not another timing sample run.

Build command:

```
RUSTFLAGS='-C link-arg=-Wl,--threads=4' cargo build --manifest-path tools/pv-dudect/Cargo.toml --bin diagnostic --release --offline --locked -j 4
```

Control command inside the normal admitted scope:

```
taskset -c 2 /home/dombarker/project-offloads/codex-pv-dudect-20261027/harness-target/release/diagnostic
```

Tool sources are under `tools/pv-dudect/`: `src/bin/diagnostic.rs`,
`diagnose.py`, `diagnostic_analyze.py`, `diagnostic_trace.py`. They reuse the
unmodified source-link adapter/kernel bodies and existing Cargo.lock. New
binary and CSVs stay on the host. `diagnosis/tool-source-manifest.json` pins
these files and the reused adapter; build/kernel sources under crates/ and
programs/ are unchanged. The standalone package is outside release dependency
closures; no shipped-source freeze or ELF-pin gate was triggered.

## Disposition and next deliverable

Measured: the six interleaved synthetic diagnostic controls and all crop/order
statistics above. Inspected: pinned source and addressed static instruction
bodies, with rejection dependence identified and no additional hash byte-based
branch/address found. Not proved: constant time, absence of microarchitectural
seed-value timing, a unique cause for D294, runtime-libc instruction behavior,
whole-candidate or shipped-account-route equivalence, or the privacy endpoint.

No premises changed: V374, V371 and all independent endpoint/deployment
conditions remain. Stop after this evidence/tools-only path-limited commit.
Next deliverable is **lead review of this artifact classification and decision
on a controlled original-versus-common-preparation comparison or any later
qualified V374 campaign**. Only the lead may request a future quiet window;
Stream A's 30-minute separation remains binding. This job schedules none.
