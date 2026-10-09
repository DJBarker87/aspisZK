# R-E4: exact verifier savings with equality gates

**Selected result: transfer 15,078,299 CU; withdrawal 15,070,869 CU.** This
saves 4,257,383 / 4,254,657 CU (about 22.0%) against R-E3. Heap high-water is
131,032 bytes. Both regenerated proofs and public contexts are byte-identical
to R-E3; all 1,894 rejection records are unchanged. The selected SBF stack gate
has zero reachable diagnostics. All requested 1.4M acceptance runs still exhaust
during Semantic. The completed numbers are explicitly **DIAGNOSTIC**, not
one-transaction acceptance.

Base: `origin/v8-reference` at `5770f37aee1eb05332081a51774209263f1c7b6a`.
Branch: `codex/r0-e2e-re4-20261009`. Selected implementation plus retained audit
feature: `52df8fc21ace0d3a299b4272e195c0bcc9831e9f`.
The best cumulative stage is S4; the R91 candidate is retained behind the
**default-off `r0-r91-audit` feature** because it regresses to 22.04M CU.
No prover algorithm, wire, challenge, check order or acceptance predicate was
changed. No §8 protocol step, D14 row, continuation protocol or Lean change
was implemented. No network deployment or transaction occurred.

## Cumulative measured results

Each arithmetic change passed the native R-E3 differential before its SBF
measurement. Each executed stage has one successful build, both fixtures ×5
at 1.4M, and one DIAGNOSTIC execution per fixture at 200M. There are no repeated
unchanged measurements. The three failed R91 code-generation variants produced
no measurements; their changed source snapshots and logs are retained below.

S1: checked subfield chord; S2: tensor update; S3: outer Karatsuba;
S4: V2 transpose onto F; S5d: outlined R91 arithmetic, audit only.
Negative incremental saving means a regression. Merkle/V1 columns sum all
22 individually marked fibres. The total includes entry/tail overhead outside
the five phase groups.

| Stage | Fixture | Semantic | ChordClaims | Merkle ×22 | V1 ×22 | V2 | Total | Incremental saving |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| re3 | transfer | 2,693,892 | 1,008,549 | 641,001 | 3,476,468 | 11,507,624 | 19,335,682 | 0 |
| re3 | withdrawal | 2,689,719 | 1,007,824 | 641,165 | 3,475,098 | 11,503,624 | 19,325,526 | 0 |
| s1 | transfer | 2,693,892 | 1,008,644 | 641,001 | 3,047,614 | 9,082,171 | 16,481,470 | 2,854,212 |
| s1 | withdrawal | 2,689,719 | 1,007,919 | 641,165 | 3,046,275 | 9,078,171 | 16,471,345 | 2,854,181 |
| s2 | transfer | 2,693,892 | 1,008,644 | 641,001 | 3,047,614 | 8,300,336 | 15,699,635 | 781,835 |
| s2 | withdrawal | 2,689,719 | 1,007,919 | 641,165 | 3,046,275 | 8,296,499 | 15,689,673 | 781,672 |
| s3 | transfer | 2,647,122 | 968,572 | 641,001 | 3,010,106 | 8,137,088 | 15,412,037 | 287,598 |
| s3 | withdrawal | 2,642,844 | 967,918 | 641,165 | 3,008,755 | 8,132,594 | 15,401,372 | 288,301 |
| s4 | transfer | 2,647,122 | 968,572 | 641,001 | 3,010,106 | 7,803,350 | 15,078,299 | 333,738 |
| s4 | withdrawal | 2,642,844 | 967,918 | 641,165 | 3,008,755 | 7,802,091 | 15,070,869 | 330,503 |
| s5d | transfer | 3,400,620 | 1,226,117 | 641,001 | 4,019,047 | 12,743,485 | 22,038,418 | -6,960,119 |
| s5d | withdrawal | 3,394,676 | 1,225,538 | 641,165 | 4,016,281 | 12,744,991 | 22,030,747 | -6,959,878 |

Raw per-fibre markers for **every stage and both fixtures** are in
[summary-4.json](re4/summary-4.json), with the original execution logs in
`s1-…s4-diagnostic/` and `s5d-diagnostic/`. The main table reports measured CU,
not sums of primitive estimates.

## Exact changes and reference gate

1. `onchain::subfield_line` constructs the same generic secant, checks that
   all three high QM31 components are zero, and returns `WrongField` otherwise.
   The prepared line stores QM31 coefficients. V1 evaluates its denominator
   in QM31, uses the non-panicking QM31 inverse and E×K numerator product.
   The structured quotient and the two image rows use `mul_qm31`.
   The generic E route is retained in the native reference module.
2. Each tensor pair computes `right = v*x`, `left = v-right`. This saves
   exactly 3,069 K multiplications per V2 while preserving every tensor value.
3. `WideExact::mul` uses three QM31 products at the outer layer. The native
   schoolbook method is frozen in `mul_re3`; the reference verifier selects
   it with a scoped thread-local guard. One million deterministic random
   pairs, all 64 limb-unit pairs and nine boundary pairs agree byte-for-byte.
4. V2 forms `G = dF^T F` in the existing `[0,3,2,1]` channel order, applies the
   exact chord map C by transposing the sparse column reader, and pairs CG
   with the three QM31 tensors and inactive bit table. It retains the same
   overflow correction, image rows, explicit quarter, lhs polynomial and
   final V2 predicate. The tau terms use G before its in-place overwrite.

The native-only `r0-e4-reference` feature preserves the R-E3 on-chain-shaped
algorithm in `onchain_re3.rs` and its generic structured map in
`structured_re3.rs`. Its end-to-end wrapper preserves R-E3 parsing, semantics,
authentication and check sequence. Passive trace hooks compare circle points,
opening challenges, reconstructed polynomial, gamma/alpha powers,
interpolant, every reached V1 fibre result, and both sides of V1/V2 as canonical
field bytes. The suite also compares exact errors, phase order and query sets,
and independently compares the fixed-challenge V1/V2 rejection teeth.
The semantic R91 candidate uses the old M31 expressions in reference mode.

All gates retain two honest fixtures and 1,894 recorded rejections. The final
prover ran once per fixture with the selected shared field kernels; both
95,712-byte proofs and both 1,880-byte public contexts match R-E3 exactly.
[Preservation and hashes](re4/preservation-4.json),
[final selected differential](re4/selected-native.log),
[transfer regeneration](re4/regenerate-transfer.json),
[withdrawal regeneration](re4/regenerate-withdrawal.json).
The sealed proof account remains 95,752 bytes; the signed verifier-only TxV1
proposal remains 261 bytes. Execution measurements use legacy transactions.

## V2 choice: counts before implementation

The ledger was committed in `61f27bf21` **before** implementing S4 in
`f4e1d419b`. [V2-ORDERS.md](re4/V2-ORDERS.md) and
[v2-order-counts.json](re4/v2-order-counts.json) give products, additions,
product reductions, operand normalizations, canonical add/sub reductions,
explicit vector traffic and loop sweeps for four schedules: current;
scalars outside with six dense dots; that schedule with sparse image dots;
and transpose onto F. No protocol-level batching or narrowing is involved.

| Order | E×E | E×K | E×F | K×K | Arithmetic estimate |
|---|---:|---:|---:|---:|---:|
| Current after S3 | 1,039 | 6,146 | 3,838 | 3,069 | 8,332,083 |
| Scalars outside, six dense dots | 788 | 6,144 | 0 | 15,357 | 13,331,909 |
| Scalars outside, sparse image dots | 788 | 4,098 | 1 | 15,357 | 11,746,594 |
| **Transpose onto F** | **788** | **6,146** | **3,838** | **3,069** | **7,978,749** |

Transpose has the lowest arithmetic estimate, with 66,592 more explicit vector
bytes than current. Its predicted improvement is 353,334 CU; measured transfer
improvement is 333,738 CU. The native counter subsequently matches **every
counted primitive exactly on both fixtures**:
[v2-count-validation.json](re4/v2-count-validation.json).
The tested schedules do not support the plan's 6.5–7M estimate; selected V2
measures 7.803M. The counts do not price memory traffic or claim to exhaust all
possible equivalent implementation schedules.

## Karatsuba primitive calibration

The changed E×E primitive alone was measured at N=64 and N=128, subtracting
its matching empty loop, using the R-E2 harness. Four local transactions and
four matching simulations agree; the returned bytes also match R-E2.
Other unchanged primitives were not remeasured.

| N | R-E2 CU/product | R-E4 CU/product | Saving |
|---:|---:|---:|---:|
| 64 | 1,466.453125 | 1,311.875000 | 154.578125 |
| 128 | 1,466.562500 | 1,312.1953125 | 154.3671875 |

[Primitive data](re4/s3-primitive-costs.json),
[return-byte comparison](re4/primitive-preservation.json),
[million-pair gate](re4/s3-field.log),
[primitive stack audit](re4/s3-primitive-stack/stack-audit.json).
The end-to-end S3 saving is only 287,598 / 288,301 CU; this measurement
supersedes the larger planning estimate.

## Semantic kernels: applicability and rejected performance candidate

- **R60 inverse chain is already present.** `M31::inv` already implements the
  38-multiplication fixed chain; the inherent CM31/QM31 norm inverses and
  circle parameterization already call it. The R0 semantic path was not
  using a missing copy of that kernel. No redundant port or claimed saving.
- **R218 is not an unchanged semantic kernel for this path.** Its five norm
  coefficients evaluate four affine circle sign fibres. R0's semantic
  verifier has no such affine four-denominator call; its terminal and two
  rational circle samples do not fit that input shape. Introducing it here
  would change the algorithm beyond this requested port. It was not applied.
- **R91 was ported and measured, then deselected.** The existing bounded-u64
  add/sub fast paths and original raw-u32 fallback expressions preserve
  overflow/underflow behavior under the selected compiler profile. One
  million canonical add/sub pairs match both R-E3 and independent modular
  arithmetic; 128 raw outcomes match, including any panics. The full fixture
  and rejection differential also passes.

The first R91 build (`s5`) fails in `aspis-statement` with LLVM
`Branch target out of insn range`. Allowing compiler-chosen inlining (`s5b`)
and removing cold fallback placement (`s5c`) do not resolve it. Explicit
M31 call boundaries (`s5d`) compile and pass the complete stack gate.
Every revision changes source layout, reruns its native gate, and gets one
SBF build. None changes arithmetic, formula, check order, caps or toolchain.
All three failed source files, source manifests, build logs and resource
receipts are preserved; there was no unchanged retry.

The valid S5d candidate **adds 6,960,119 / 6,959,878 CU** against S4.
Its Semantic phase alone rises to 3,400,620 / 3,394,676 CU. Consequently
`r0-r91-audit` is default-off and available through core, statement, prover
and verifier manifests for review. The chosen default retains S4.
The hoped-for ≥1M semantic recovery was not obtained. No different semantic
formula was substituted to manufacture that result.

The final feature-selection build has identical executable `.text`, `.rodata`,
relocations, dynamic data and symbol sections to measured S4. Its only two
section-content byte differences are panic source-line numbers in
`.data.rel.ro` (M31 inverse nonzero and dot-length assertions); neither is
used by either successful diagnostic execution. Therefore S4 measurements
are reused, without an unchanged rerun.
[Executable comparison](re4/selected-artifact-equality.json),
[all section differences](re4/selected-section-equality.json).

## Acceptance, stack, heap and resource evidence

Each measured stage's acceptance series is both fixtures ×5 at 1,400,000 CU.
All 50 runs exhaust during Semantic, with last completed marker `parsed`.
Each transaction consumes 1,400,000 CU; the verifier log reports 1,399,644.
For the selected S4 series the parsed-marker remaining CU is 1,392,074 /
1,392,126. The completed diagnostic budget is 200M, with the same 256 KiB
heap and otherwise pinned LiteSVM 0.16.0 / Agave 4.2.1 settings. Diagnostics
are not acceptance claims; no completed phase CU is inferred from aborts.

All successfully executed builds, including the rejected R91 candidate, have
zero reachable stack diagnostics under the R-E3 audit: direct-call closure
plus every linked function as a conservative target of every `callx`.
The selected build has 258 linked/reachable functions; its 55 diagnostic lines
concern 32 functions absent from the linked ELF. Full symbols, disassembly,
edges and every diagnostic classification are in
[selected stack audit](re4/selected-stack/stack-audit.json).
The R91 candidate has 267 linked/reachable functions and no reachable
reported frame. Failed R91 compilations were never executed or assigned a
successful stack audit.

Every completed stage has SBF heap high-water **131,032 bytes**, 131,112 bytes
below 256 KiB. This is the non-freeing bump cursor after V2, including the
cursor reservation, all preceding allocations and phase logging. Selected
transfer is still 13,678,299 CU above 1.4M (10.77 times the limit); withdrawal
is 13,670,869 above it. Semantic alone remains above one transaction.

All Linux build/test/generation/audit/measurement jobs run in individual
scopes with MemoryHigh=4 GiB, MemoryMax=6 GiB, MemorySwapMax=0. Reservations
are checked against a 50 GiB safe host total, and the pinned build workspace
and cache are reused. Arithmetic/proof jobs are optimized release binaries.
Expected work is compilation for build commands, SBF V2 execution for CU
runs, and optimized proof generation for regeneration; these scopes are
recorded in the measurement/finish plans. No cap was raised, no job reached
the 24 GiB or ten-minute review point, and every recorded scope swap is zero.

[Complete resource table](re4/resources-4.md) and
[resource JSON](re4/resources-4.json) record exact command, exit status, wall
time, sampled aggregate RSS, cgroup peak/swap and source revision. Each job
also has its own source manifest and reservation snapshot. The three R91
compiler failures are retained as nonzero exits; all executed measurements
and equality gates succeed. Source revisions before an implementation commit
are disambiguated by their exact per-file SHA-256 snapshots.
[Environment and retained-key permissions](re4/environment-re4.json),
[final source manifest](re4/source-manifest.json),
[artifact manifest](re4/artifact-manifest.json).

Task keys remain on the build host with mode 0600. No key was deleted,
unlinked or cleaned up; no network funds/refunds were involved. No private
key file is copied into this evidence. `#print axioms`: not applicable;
this is Rust/SBF evidence with no Lean edit or formal release claim.
The specified stop conditions were not triggered. Compiler failures and the
R91 performance regression are explicit negative results, not waived gates.
