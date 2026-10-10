# P1 arithmetic cost probe — stopped at C5 field preflight

Unproved Rust cost experiment from `origin/v8-reference` at
`f1e5ca9de668110f80c548abe5e80b43f838099f`, on
`codex/r0-cost-probe-p1-20261009`.

**No measured configuration fits 1,400,000 CU.** The lowest completed totals
are C3/C4: **16,824,071 transfer / 16,819,235 withdrawal**, with headroom to
1,300,000 of **−15,524,071 / −15,519,235 CU**. There is no first fitting
configuration. This result describes the implemented arithmetic schedules;
it does not establish a lower bound or settle whether another implementation
can reach one transaction.

**Stop:** C5(b)'s native preflight sampled α₀ in K from the same row-30 block,
while retaining C4's γ and quotient inputs. All 256 resulting F coefficients
have nonzero high K components on each fixture. Encoding that F in K would
lose data or require an additional change to shared fold inputs. This triggers
the requested shared-parts checkability stop. C5(a) and C5(c) were not started;
C5(b) has no completed configuration, rejection corpus, SBF build, or CU result.
The field-shape preflight was performed before implementing any C5 variant.

Cells below contain completed **DIAGNOSTIC CU [E/K/F multiplication counts]**.
Counts are the inclusive `r0-op-count` counters: E = EMul + EMulK + EMulF +
ESquare; K = KMul + KMulF + KMulC + KSquare; F = FMul. Here F in the count
header denotes the base field, whereas F in the protocol denotes the final
message. Nested tower operations are included; counts are not additive CU
estimates. Full inclusive and exclusive primitive counts are retained in
`c{0,1,2,3}-{transfer,withdrawal}-ops.json`.

Merkle and V1 aggregate 22 individually marked fibres. Other is the difference
between total transaction CU and the named phases, including entry, parsing,
markers, tail and compute-budget instructions. Completed diagnostics use a
200M limit. Execution is verifier-only in LiteSVM, using sealed proof/public
accounts; proof upload, Pool CPI and settlement are excluded. All reported
proof bytes are actual probe-prover output.

| Configuration / fixture | Semantic CU [E/K/F] | ChordClaims CU [E/K/F] | Merkle CU [E/K/F] | V1 / batched query CU [E/K/F] | V2 / rounds CU [E/K/F] | Other CU [E/K/F] | Total CU | Proof bytes | Headroom to 1.3M |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| C0 / transfer | 3,400,620 [311/2,592/16,330] | 1,226,148 [269/899/5,561] | 641,089 [0/0/0] | 4,019,047 [8,690/18,018/95,274] | 13,230,198 [11,023/26,156/143,148] | 8,504 [0/0/0] | 22,525,606 | 95,712 | -21,225,606 |
| C0 / withdrawal | 3,394,676 [311/2,583/16,276] | 1,225,569 [269/899/5,561] | 641,253 [0/0/0] | 4,016,281 [8,690/18,018/95,154] | 13,237,361 [11,023/26,156/143,148] | 8,452 [0/0/0] | 22,523,592 | 95,712 | -21,223,592 |
| C1 / transfer | 3,400,620 [311/2,592/16,330] | 1,211,448 [252/862/5,339] | 641,084 [0/0/0] | 4,015,524 [8,690/18,018/95,040] | 7,986,121 [1,038/15,404/86,312] | 8,504 [0/0/0] | 17,263,301 | 95,712 | -15,963,301 |
| C1 / withdrawal | 3,394,676 [311/2,583/16,276] | 1,210,939 [252/862/5,339] | 640,983 [0/0/0] | 4,015,822 [8,690/18,018/95,100] | 7,986,859 [1,038/15,404/86,312] | 8,452 [0/0/0] | 17,257,731 | 95,712 | -15,957,731 |
| C2 / transfer | 3,400,621 [311/2,592/16,330] | 1,211,457 [252/862/5,339] | 641,085 [0/0/0] | 4,015,524 [8,690/18,018/95,040] | 8,813,001 [1,566/16,732/93,256] | 9,499 [0/0/0] | 18,091,187 | 96,384 | -16,791,187 |
| C2 / withdrawal | 3,394,677 [311/2,583/16,276] | 1,210,948 [252/862/5,339] | 640,984 [0/0/0] | 4,015,822 [8,690/18,018/95,100] | 8,817,748 [1,566/16,732/93,256] | 9,447 [0/0/0] | 18,089,626 | 96,384 | -16,789,626 |
| C3 / transfer | 3,400,621 [311/2,592/16,330] | 1,261,572 [252/862/5,339] | 640,632 [0/0/0] | 2,334,544 [3,102/6,886/43,912] | 9,177,203 [1,952/17,604/98,664] | 9,499 [0/0/0] | 16,824,071 | 96,384 | -15,524,071 |
| C3 / withdrawal | 3,394,677 [311/2,583/16,276] | 1,260,976 [252/862/5,339] | 640,531 [0/0/0] | 2,334,240 [3,102/6,886/43,962] | 9,179,364 [1,952/17,604/98,674] | 9,447 [0/0/0] | 16,819,235 | 96,384 | -15,519,235 |
| C4 (C3 evidence) / transfer | 3,400,621 [311/2,592/16,330] | 1,261,572 [252/862/5,339] | 640,632 [0/0/0] | 2,334,544 [3,102/6,886/43,912] | 9,177,203 [1,952/17,604/98,664] | 9,499 [0/0/0] | 16,824,071 | 96,384 | -15,524,071 |
| C4 (C3 evidence) / withdrawal | 3,394,677 [311/2,583/16,276] | 1,260,976 [252/862/5,339] | 640,531 [0/0/0] | 2,334,240 [3,102/6,886/43,962] | 9,179,364 [1,952/17,604/98,674] | 9,447 [0/0/0] | 16,819,235 | 96,384 | -15,519,235 |
| C5(a), both fixtures: not run after stop | — | — | — | — | — | — | — | — | — |
| C5(b), both fixtures: field preflight stop | — | — | — | — | — | — | — | — | — |
| C5(c), both fixtures: not run after stop | — | — | — | — | — | — | — | — | — |

C0 applies checked subfield secant coefficients (`c1 == 0`), E×K operations
in the structured transpose and image rows 1021–1023, K line-word inversion
in V1, tensor right = v×x / left = v−right, outer Karatsuba, and R91
bounded-u64 add/sub with the original raw-input fallback. R60's inverse chain
was already present and is retained behind an equality gate. R218's affine
four-denominator input shape is absent from R0's semantic path; no alternative
semantic formula was substituted. The separate R-E4 V2 transpose is excluded.
The combined exact-change configuration is **3,189,924 / 3,198,066 CU more
than the existing R-E3 totals**; it produces no net saving with R91 enabled.
No new component ablation is claimed.

Both C0 proof/public pairs equal R-E3 byte-for-byte
([proof equality](c0-proof-equality.json)). Both accept natively; all 1,894
rejection records equal R-E3 ([rejection equality](c0-rejection-equality.json)).
The native gate compares canonical field traces, challenges, query sets,
phase boundaries and errors, and cross-checks the instrumented R-E3 copy
against the untouched R0 wrapper. Karatsuba passed one million random pairs,
all 64 limb-unit pairs and nine boundary pairs. R91 passed one million
canonical pairs and 128 raw outcomes; R60 matched generic exponentiation on
4,098 inputs. C0 heap high-water is 131,032 bytes. Its C0-only result was
recorded in `faa587bab` before C1 work.

C1 samples κ and τ with `qm31_sample` from unchanged row-28/29 blocks. Weight
tensors, the chord transpose and image terms use K; the final pairing uses E.
The prefix through v and transcript states through row 29 equal C0 bitwise;
K samples equal the low K components of the predecessor's E samples. Shared
field traces and rejection outcomes match the full-width arithmetic oracle.
Both honest proofs accept, each has 95,712 bytes, and all 1,894 corpus records
match C0. Heap is 90,072 bytes. C1 evidence was recorded in `db0577b9f`.

C2 appends three degree-six relation records (3×7 E values, 672 bytes) after
the unchanged C1 proof. Labels 0xc1–0xc3 bind each polynomial before its E
challenge. The initial dual weight carries R0's quarter; later rounds use
unscaled dual folds. Each boundary checks c0+c4=incoming and the terminal
dot has four terms. The native prover checks the dot identity after each fold.
Every C1 proof byte is preserved. All 21 new coefficient mutations replace
21 redundant later-fibre leaf mutations per fixture, keeping 1,894 total
rejections. Both native acceptances and shared-field gates pass.

**C2 implementation limitation:** the verifier still constructs the 1,024 K
primary weights and folds them explicitly. The small terminal dot does not
remove that work. This is why the table must be read as the measured schedule,
not as the cost of a fully contracted tensor evaluator. No compact evaluator
or lower-bound claim is supplied. Heap is 106,456 bytes; C2 evidence was
recorded in `5af2d4fbd`.

C3 samples ρ in E after the original query set, accumulates the 22 opened fold
values with powers ρ¹…ρ²², absorbs that scalar, and injects its query functional
into relation round 1. It removes the 22 separate final-message evaluations
and comparisons from the SBF path. Query-functional terminal weights use
three four-entry contractions per query and a four-entry terminal contribution.
Native gates compare this computation with the dense 256-entry functional,
and the opened batch with all 22 direct evaluations. A fixed-challenge D-leaf
mutation changes the batch and rejects at the relation. Both honest proofs
accept; 1,894 rejection cases pass; the shared pre-tail bytes equal C2.
C3 retains C2's dense primary-weight construction. Heap is 106,456 bytes;
evidence was recorded in `54741cffa`.

C4 reuses C3's **exact artifact and evidence, with zero new executions**
([reuse record](c4-reuse.json)). Eight-way Merkle was already present at the
requested base: `Path = [[Digest; 7]; 6]`, with eight ordered children per
parent hash. A two-swap permutation alone leaves the current explicit-vector
loops, buffer sizes and field-operation counts unchanged, so that optional
transport-only change was omitted. A compact two-swap evaluator was not
implemented; the older sparse-G/channel evaluator was not substituted.

The C5(b) observations retain γ, α₀ in E and K, nonzero component counts,
and the first four quotient coefficients plus their folded value for each
fixture ([transfer](c5-narrow-transfer-observation.json),
[withdrawal](c5-narrow-withdrawal-observation.json)). The passive observation
hook regenerated exactly the retained C3 proof bytes. A separate integer
polynomial oracle, using i²=−1, u²=2+i and v²=u, independently reproduces the
first non-K coefficient on each fixture
([witness check](c5-independent-witness.json)). This is a concrete obstruction
for these requested shared inputs, not an impossibility claim about other
field schedules. No projection, γ narrowing, or replacement fold was made.

Across C0–C3, each fixture ran **five times at 1,400,000 CU**: 40 executions
in total, all exhausting in Semantic after `parsed`. Each configuration also
has one completed diagnostic per fixture. Acceptance-limit failures do not
supply completed phase CU. The call-graph audits conservatively treat every
linked function as a target of each indirect call. C0/C1/C2/C3 have
271/276/283/286 linked functions, respectively, and **zero reachable stack
diagnostics**. Every heap high-water is below 262,144 bytes. Stripped and
unstripped ELF text hashes match; ELFs, symbols, disassembly and audits are
retained under the corresponding `cN-elf/` and `cN-stack/` directories.

All 59 build-host jobs have individual scopes with MemoryHigh=4 GiB,
MemoryMax=6 GiB and MemorySwapMax=0. Aggregate reservations were checked
against 50 GiB before each launch. Maximum sampled aggregate RSS was
**1,257,656,320 bytes**, maximum cgroup memory peak **998,129,664 bytes**,
and every recorded scope has zero swap. Three compilation failures are
retained: C0 driver fixture imports, C1 K-power helper types, and C2 encoder
borrow lifetime. Each replacement followed a source change. There were no
memory-cap increases, memory kills, or unchanged measurement reruns.

[Resources](resources.json) records each exact command, exit status, wall
time, peak RSS, cgroup peak/swap and source revision. Per-job source manifests
pin exact inputs, including uncommitted inputs in the first C0 gate; a revision
alone is not used as their source identity. The current
[source manifest](source-manifest.json), [artifact manifest](artifact-manifest.json),
[environment](environment-final.json), and [evidence audit](evidence-audit.json)
provide the final index. Native proof generation and arithmetic gates use
optimized Rust. The C5 native runs spent their time in proof generation;
the generic launcher plan's “SBF verifier arithmetic or read-only evidence
audit” label for those two runs is inaccurate and is corrected here.

Original `r0/onchain.rs`, the original R0 modules and reference prover,
reference fixture files, and every Lean file remain byte-identical to the
requested base ([preservation manifest](preservation.json)). Shared field
changes are opt-in; default multiplication retains its original formula.
No Lean was run; `#print axioms` is not applicable. Task keys remain on nuc
with mode 0600; none was removed or included in the report artifacts. No
network transaction was sent.

A documentation-only P1′ preflight was interleaved on this branch at
`e72f163b5`. Its original text is preserved in
[REPORT-P1-PRIME-INTERLEAVED.md](REPORT-P1-PRIME-INTERLEAVED.md), and the
historical C0/C1 report remains in
[REPORT-P1-PRE-PRIME.md](REPORT-P1-PRE-PRIME.md). Neither the separate P1′ base
nor its S4 numbers is used in this P1 table. This report follows the requested
`f1e5ca9de` experiment.
