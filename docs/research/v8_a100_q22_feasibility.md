# V8-A100 direct-q22 two-point-DEEP feasibility investigation

Date: 2026-09-07
Classification: **C — promising but not yet established**

## Executive verdict

The best profile found is still the proposed **q22, 26-byte digest, two component-wise OOD points** profile. It has an exact maximum proof body of **39,934 bytes** and a complete pair-verifier account size of **40,662 bytes**. Under the explicitly named `Q = 2^36`, `R = 259`, and 1,511-verifier-call research resource envelope, the corrected exact rational raw-error ledger is **104.26208146248575 bits** without crediting proof of work. Lean proves that conditional ledger is at most `2^-104` and not at most `2^-105`.

That is not yet a production theorem. Four independent release gates remain open:

1. the exact compiler replay/classifier now constructs a restoration-wide partial K1.4 provider, but the production parsed-proof type is still V7/q16 and carries neither V8 component vector nor a q22 schedule, so the V8 parser/transcript/source correspondence is absent;
2. the verifier checks two gamma-compressed OOD scalars, not all 58 component values.  Lean now proves the correct conservative bad-gamma cardinality `100*28 = 2,800`, but that scalar check is not yet connected to an accepting V8 source replay;
3. a legal Frobenius-conjugate OOD pair disproves the former ambient-rank-108 hiding target (`got 104`).  Lean proves the correct legal-image-containment criterion and exact hiding from it, but the actual witness/mask maps are not yet proved to satisfy containment for every legal schedule and both settlement layouts;
4. a capped Linux/x86_64 host reproduced the V7 transaction baseline and the research refactor reduced the reachable V8 quotient frames from 11,904/18,880 bytes to 2,176/2,112 bytes.  The isolated probes nevertheless cost 807,012 CU (heap-batched) and 791,539 CU (pointwise), canonical parsing alone cost 634,879 CU, a production-facing helper still has a 4,736-byte frame, and there is no complete V8 verifier or honest V8 transaction-CU number.

A continuation on this branch has now closed the former circle-code gate. Lean constructs the affine-chord quotient in both the distinct-x and equal-x branches, proves the exact component degree drops, and proves that the adaptive width-29 quotient is represented by an actual 1,024-entry natural-basis message consumed by the deployed initial encoder. This makes the existing source-connected circle-to-line fold commutation theorem applicable; it is no longer an ordinary-polynomial-only claim.

These are precise proof and integration obligations, not evidence of impossibility. The scalar-gamma repair still clears 104 bits by a wide margin, the hiding counterexample invalidates a proof target rather than hiding itself, and the SBF failure is an implementation-shape defect rather than a measured CU ceiling. Consequently this work does not claim A or B, and it does not classify the candidate as D.

## 1. Repository and base selection

| Item | Value |
|---|---|
| Original checkout | `/Users/dominic/ZK` |
| Research worktree | `/Users/dominic/ZK/.worktrees/ZK-v8-a100-q22-deep-feasibility` |
| Research branch | `research/v8-a100-q22-deep-feasibility` |
| Exact base | `87a1b80e34a14eefca0111aae54a4893e85ad0a2` |
| Base parents | `6971d0c18c12488695808790afa2cf025ef9526a`, `d42334b89de4ec3b18839580e9c17bec5b804a91` |
| Toolchains observed | Rust 1.93, Lean 4.32, Solana 2.3 |
| Research hosts | Darwin arm64 for source/focused proofs; task-owned capped directory on Linux x86_64 NUC for SBF/LiteSVM |

The base is the merge `merge: integrate cutoff-20 q16 publication policy [skip ci]`. Its first parent contains the advanced exact K1.2–K1.6 work, while its second parent contains the most recent relevant production V7 first-cap-203/cutoff-20 implementation and CU evidence available when the worktree was created. This avoided silently combining incompatible topic branches.

Relevant recent branches at selection/review included:

| Branch | Tip | Relevance |
|---|---:|---|
| `main` | independently advanced through `4c91f97a` to `b053663d` during the investigation | Production/formal integration continued after the research base was selected. The research branch was not rebased; the single relevant accepted-fold source-chain commit was explicitly cherry-picked as local `e39f8b37`. |
| `integration/v7-cutoff20-main-20260902` | `4420d842` | Cutoff-20 integration. |
| `research/v7-first-cap203-scan-cu-fix-20260902` | `d42334b8` | Exact current-binary frontier/CU work and one parent of the selected merge. |
| `research/v7-deposit-invariant-promotion-20260902` | `44602d36` | Pool transaction evidence. |
| `integration/v7-persisted-lane-closure-candidate-20260902` | `7e0f5aac` | Persisted-lane/source closure work. |
| `research/v7-persisted-lane-source-formal-closure-20260901` | `0ed3f0b1` | Exact Pool source formalization. |

The original checkout was not modified by this investigation. At worktree
creation its user-owned dirty work included
`AspisFormal/AspisFormal/K1/V7Tag73K13CorrectedAlphaGammaClosure.lean` and
untracked `AspisFormal/AspisFormal/K1/V7Tag73K13CorrectedAlphaPairEquality.lean`.
It later advanced independently to `b053663d` and accumulated a larger
unrelated V7/transcript change set while this work ran; none of it was staged,
overwritten, or committed here. All V8 changes were made in the separate
worktree and on the separate local branch. Nothing was pushed, merged,
deployed, or published.

Local milestone commits before this report:

| Commit | Subject |
|---:|---|
| `94256d17` | `research: audit v7 wire arithmetic and add direct q22 profile` |
| `c0548a76` | `formal: prove q22 direct-sampler and maximum frontier bounds` |
| `52fc3bc5` | `formal: model two-point component deep quotient` |
| `7c6791d1` | `formal: establish or isolate pre-gamma tuple binding` |
| `5bc9e2c4` | `research: prototype v8 two-point deep verifier` |
| `e03003d6` | `formal: correct v8 deep quotient to the circle chord` |
| `d42afb5c` | `bench: attribute v8 deep host path and record sbf gate` |
| `54fe3b94` | `formal: assemble conditional v8 raw error parameter sweep` |
| `87d19e02` | `research: add v8 q22 two-ood hiding rank witnesses` |
| `1c111825` | `evidence: retain focused v8 proof and v7 baseline logs` |
| `00ad1d3d` | `research: compute exact v8 gamma security thresholds` |
| `e39f8b37` | `proof: retain accepted fold source chain` (explicit cherry-pick of `4c91f97a`) |
| `598a8e98` | `formal: connect v8 chord quotient to circle encoder` |
| `2910cfc3` | `research: cover v8 equal-x deep branch` |
| `e8627859` | `docs: close v8 circle-code feasibility gate` |
| `0276264f` | `formal: isolate v8 hiding image criterion` |
| `68a74c7b` | `formal: construct fallback-free pre-gamma k14 replay` |
| `cf787f7f` | `research: extend v8 hiding counterexample to pair forest` |
| `1e1f1752` | `evidence: record v8 hiding rank counterexample` |
| `f486fff7` | `formal: correct v8 scalar-deep raw ledger` |
| `c67d0a29` | `evidence: retain v8 pre-gamma replay audit` |
| `156097c4` | `bench: reproduce v7 linux baseline and isolate v8 stack gate` |
| `2bddfcb4` | `formal: bound v8 scalar-fingerprint gamma family` |
| `299ac988` | `formal: expose v8 scalar gamma bound` |
| `6ff1e1c2` | `research: record v8 scalar-prefix evidence` |
| `2aaca2bc` | `research: probe v8 per-c1 hiding image containment` |
| `98f3831a` | `evidence: isolate v8 per-c1 source translation gap` |
| `ec74d86f` | `formal: connect v8 ledger to scalar gamma theorem` |
| `d4ba99b0` | `evidence: resolve v7 canonical audit body delta` |
| `c9c09913` | `research: add stack-safe v8 deep SBF probes` |
| `80547009` | `research: stream v8 gamma dots below SBF stack limit` |
| `db797408` | `bench: add isolated v8 deep LiteSVM harness` |
| `42dbe457` | `research: bind v8 SBF probe challenges through transcript prefix` |
| `d313a968` | `research: split v8 transcript and probe stack frames` |
| `69098fe5` | `bench: separate v8 parse and quotient CU phases` |
| `615b700d` | `bench: record v8 SBF stack and CU evidence` |

The final documentation commit is intentionally identified by subject rather than embedding its own hash in itself.

## 2. V7 baseline

### Source map

The baseline audit followed the production path through:

- `crates/aspis-core/src/v7_onefold.rs` and `v6_onefold.rs` for the wire, profile binding, Merkle frontier, field packing, and schedule;
- `crates/aspis-core/src/transcript.rs` for challenge squeezing and bounded sampling;
- `crates/aspis-prover/src/v6_onefold_prover.rs` for proof construction;
- `programs/aspis-verifier/src/processor.rs` and the Pool terminal paths for verifier/settlement composition;
- the Merkle-208 implementation and the first-cap-203 query selection logic;
- the exact K1.2–K1.6 source, scheduler, restoration, compiler, and capstone modules, including the current equivalents of the named pre-gamma and measured-assembly files;
- the committed LiteSVM/Agave/SBF measurement reports and release replay scripts.

### Reproduced host tests

| Gate | Result | Evidence |
|---|---|---|
| Core V7-targeted Rust suite | PASS, 33 tests | `results/v8-a100-q22/rust-v7-baseline.log` |
| Release V7 prover fixture | PASS, 1; 2 RAM-heavy NUC gates ignored by their own annotations | `results/v8-a100-q22/rust-v7-prover-baseline.log` |
| Honest fixture | body 30,400; selected counter 5; frontier 201; 13.61 s | same log |
| Release prover command overall | 47.01 s; maximum RSS 584,515,584 bytes; zero swaps | same log |

The source-derived packed `v7_onefold.rs` maximum body is **30,504 bytes**.
The apparently contradictory 30,824/30,772-byte transaction fixtures use the
default-off `v7-fixed-canonical-audit` grammar: it expands 641 fixed QM31 values
from 9,936 packed bytes to 10,256 canonical bytes, an exact **+320-byte** audit
trade while copying roots, nonces, queries, salts, and frontiers byte-for-byte.
Thus the same-page frontier-203 fixture is 30,824 canonical / **30,504 packed
equivalent**, and rollover frontier-202 is 30,772 canonical / **30,452 packed
equivalent**.  The baseline discrepancy is resolved; the larger numbers must
not be reported as the production packed grammar.

### Formal baseline

The selected base records the exact measured K1.6 capstone as a successful historical release replay: 2.87 s, 6,706,000 KiB maximum RSS, zero swap, with only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` axioms. A local targeted rebuild could not begin because the shared cache lacked `V7Tag73ExactRestoredConcreteK16Assembly.olean`; the main checkout's cache also lacked the exact restored and capstone objects. A cold dependency rebuild was not used as a local theorem-discovery step. Focused V8 successors instead used a revision-matched ignored cache overlay, and each process remained below 8 GiB.

### Existing SBF/CU evidence at the selected source lineage

| Shape | CU | Status |
|---|---:|---|
| V7 withdrawal, same page | 1,136,135 | Frozen actual transaction evidence. |
| V7 withdrawal, rollover | 1,201,757 | Frozen actual transaction evidence. |
| Current-binary worst frontier 202, verifier only | 1,084,738 | Actual measurement in the cutoff-20 audit. |
| Current-binary worst frontier 202, rollover transaction | 1,218,972 | Actual measurement in the cutoff-20 audit. |
| Modeled frontier 203/cutoff 20 envelope | 1,299,084 | Calibrated envelope, not an executed exact maximum fixture and not promoted here to measured fact. |
| Finalized live rollover transaction | 1,196,956 total; 1,125,340 verifier | Actual finalized evidence; profile upload reported as 30,772 bytes. |

A later repository-host audit found the Linux/x86_64 NUC recorded in `.superstack/learnings.md`.  Fresh SBF builds and strict-work LiteSVM V7 transactions were therefore rerun in task-owned directories with zero-swap systemd scopes.  They measured **1,153,267 CU** same-page and **1,218,981 CU** rollover; the verifier CPI figures were 1,085,276 and 1,084,747 CU respectively.  Exact toolchain, hashes, commands, RSS, and three resolved launch failures are retained in `results/v8-a100-q22/sbf-linux-baseline-20260907.md` and JSON.  No RPC, deployment, live program, or live account was touched.

## 3. Source-derived wire arithmetic

The initial 608-byte query premise is false. The checked V6/V7 constants give:

```text
C1 = ceil(26 columns * 4 slots * 31 bits / 8) = 403 bytes
C2 = ceil(3 columns * 4 slots * 4 limbs * 31 bits / 8) = 186 bytes
salt = 32 bytes
query record = 403 + 186 + 32 = 621 bytes
```

The executable audit and Rust compile-time assertions tie these values to the current source constants. A change to the V6/V7 counts breaks the V8 build rather than silently changing this report.

| Field | V7 q16 | V8 q22/two OOD vectors |
|---|---:|---:|
| Fixed QM31 values | 641 | `641 - 2 + 2*29 = 697` |
| Fixed packed bytes | 9,936 | 10,804 |
| Two 26-byte roots | 52 | 52 |
| Work nonces | 24 | 24 |
| Query section | `16*621 = 9,936` | `22*621 = 13,662` |
| Body without frontiers | 19,948 | 24,542 |
| Max frontier/tree | 203 policy cap | 296 theorem maximum |
| Two frontier bytes | 10,556 | 15,392 |
| Maximum proof body | **30,504** | **39,934** |
| Proof-account header | 40 | 40 |
| Candidate after-state | 688 | 688 |
| Complete pair-verifier account | 31,232 | **40,662** |

The two vectors replace two existing scalar QM31 values, so their exact increase is 56 QM31 values: `56*4*31/8 = 868` packed bytes. Because 697 values occupy exactly 10,804 packed bytes, no independent per-value byte rounding is used.

## 4. Binary-frontier maximum, expectation, and fixtures

For a depth-`d` binary tree and `q > 0`, let `m = ceil(log2 q)`. The exact maximum minimal authentication frontier is

```text
q * (d - m) + (2^m - q).
```

The proof bounds occupied blocks at every tree level by `min(q, 2^(d-level))`, telescopes the signed level balance, and sums the capacities. It is not a random-test argument. The Lean source-model theorem proves the q22 bound from those capacity facts, while the Rust implementation reuses the production `binary_frontier_nodes` routine. The explicit q22 fixture proves tightness in both languages.

| q | Exact maximum | Exact-uniform expected frontier/tree |
|---:|---:|---:|
| 16 | 224 | 210.4947891228 |
| 17 | 236 | 222.1182624913 |
| 18 | 248 | 233.6569227415 |
| 19 | 260 | 245.1154859802 |
| 20 | 272 | 256.4981704772 |
| 21 | 284 | 267.8087716495 |
| 22 | **296** | **279.0507228208** |
| 23 | 308 | 290.2271449118 |
| 24 | 320 | 301.3408874317 |

The expected values are exact rationals in `parameter-sweep.json`; decimals are display-only.

The q22 fixtures are:

- unusually compact: positions `0..21`, frontier 15;
- deterministic typical KAT: `[231696,190946,246950,53197,7289,54330,114496,152078,187153,79950,88748,246054,172132,101489,123716,95860,205063,89983,87425,129527,252951,48626]`, frontier 282;
- high: the maximum fixture with the second entry changed from 16,384 to 8,192, frontier 295;
- exact maximum: `[0,16384,32768,49152,65536,81920,98304,114688,131072,147456,163840,172032,180224,188416,196608,204800,212992,221184,229376,237568,245760,253952]`, frontier **296**.

## 5. Query probability and sampler law

For bad set size 9,557 in the `2^18 = 262,144` fibre domain, the exact reduced probabilities are:

| q | Exact reduced probability | `-log2` bits |
|---:|---|---:|
| 20 | `42365401009061590799535716341090891933132537190657 / 2510170507564195401568191123918694774903673694978188944652555401019961976750080` | 95.5808135918 |
| 21 | `644400046927305249529780106451329882561858065689467 / 1049403403707746659394992871078251912562760069573305899406868312499133194886184960` | 100.3613837168 |
| 22 | `332233934228956685743727459727502257791407791653047 / 14872013861920722188613414594812101323350365360984194543156711866198653246277652480` | **105.1420996194** |
| 23 | `90510016082088628530469752242906686515459236954622947 / 111379486214696672614963584583466789230835556261482829772609246508334953892022594953216` | 109.9229613153 |
| 24 | `143820415554438830734916436313978724873064727520895862783 / 4865817051013751087084478292433816376662641140469356803804351384001877741521809101955321856` | 114.7039688205 |

Each is exactly `C(9557,q) / C(262144,q)`; the unreduced binomial integers are also retained in the JSON artifact.

The production sampler takes masked exact u32 draws, keeps the first occurrence of each position, and stops after a fixed 64-draw budget. For ideal independent uniform draws:

- conditioned on returning q distinct positions, every ordered injection has the same probability;
- forgetting order therefore gives the uniform q-subset law;
- exhaustion is verifier rejection, not acceptance or a retry controlled by the prover;
- the unconditioned probability of a successful bad schedule is at most the ideal hypergeometric probability, so no success-conditioning denominator is needed in the soundness ledger.

Lean instantiates the existing exact bounded-sampler theorem for q22/64 draws. The remaining correspondence obligation is to connect the translated literal transcript implementation to that existing ideal source model. V8 has one direct continuation: there is no candidate counter, 64-candidate compact-frontier selection, hidden prover choice, or accepted cloned branch.

## 6. Parameter sweep

### q sweep at 26-byte digest and two OOD points

| q | Frontier max | Body bytes | Complete account | Query bits | Conditional ledger bits | Assessment |
|---:|---:|---:|---:|---:|---:|---|
| 21 | 284 | 38,689 | 39,417 | 100.3614 | 100.3179 | Meets 100 only, with little theorem margin. |
| 22 | 296 | **39,934** | **40,662** | 105.1421 | **104.2621** | Best balance; only option near 40 KB that reaches 104. |
| 23 | 308 | 41,179 | 41,907 | 109.9230 | 105.3318 | Adds 1,245 bytes and query/Merkle work for about 1.07 bits. |
| 24 | 320 | 42,424 | 43,152 | 114.7040 | 105.3907 | Dominated by algebraic terms; adds only about 0.059 bits over q23. |

### Digest sweep for q22/two OOD points

| Digest | Body | Complete account | K1.2 bits | Conditional total bits |
|---:|---:|---:|---:|---:|
| 26 B / 208 bits | **39,934** | **40,662** | 120.9553 | **104.2620814625** |
| 27 B / 216 bits | 40,528 | 41,256 | 128.9553 | 104.2620950246 |
| 28 B / 224 bits | 41,122 | 41,850 | 136.9553 | 104.2620950776 |
| 32 B / 256 bits | 43,498 | 44,226 | 168.9553 | 104.2620950778 |

At the stated resource envelope, 208-bit Merkle digests are not the bottleneck. Widening by one byte costs 594 maximum-body bytes because both roots and both worst-case frontiers grow, but gains only about 0.0000136 total bits. A 208-bit nominal birthday heuristic alone would be inadequate; the result above instead uses the exact K1.2 multi-target term. If the actual source resource envelope is later larger, this conclusion must be recomputed.

### Two versus three OOD points

A third 29-QM31 vector adds 449 packed bytes. At q22/digest26, body/account become 40,383/41,111 bytes. No mathematical failure found in the two-point fingerprint theorem requires it, and the conservative ledger deliberately gives it no extra credit. It is therefore dominated unless the source replay or universal-hiding proof reveals a specifically three-point obstruction.

### Mask sweep

The unchanged production mask dimensions passed the original generic pair and pair-forest witnesses, but the ambient-surjectivity target itself is false for a legal Frobenius-conjugate OOD pair: actual raw-C1 rank is 104, not 108, in both layouts.  This is not a hiding failure because the legal witness image obeys the same Frobenius relation.  “Zero extra mask bytes” remains a candidate only under the corrected legal-image-containment theorem; ambient rank must not be used as the release criterion.

## 7. Transcript order and causality

The current deployed order samples gamma before the two scalar OOD values. Merely replacing those scalars with component vectors there does not give the required pre-gamma tuple fingerprint.

The research prototype uses the strongest adaptive order compatible with the intended argument:

```text
existing pre-OOD prefix
zeta0
absorb component vector 0
zeta1, sampled from the state containing vector 0; reject equality with zeta0
absorb component vector 1
check and absorb existing batch work
gamma
folding, final work, direct q22 schedule, authentication, terminal checks
```

Sampling `zeta1` after vector 0 is necessary for the sequential Fiat–Shamir bound against a prover that could otherwise choose the first vector after seeing both points. Gamma remains after batch work; the helper returns a continuation before gamma specifically to prevent accidental reordering.

The order is coherent at the abstract transcript and Rust-prototype levels. It is not yet proved equivalent to all compiler restoration/fork paths. The exact routed replay used by the new partial K1.4 provider includes the compiler's cached/fresh/advance behavior; cached replies are inert and fresh/advance replies resume the actor.  What remains missing is the V8 parsed message and post-return filter at the source boundary. Raw history occurrence is weaker than semantic prefix replay and was not accepted as a substitute.

## 8. Why the old point claims do not imply a 28-gamma bound

The existing large bad-gamma cap is **336,869,026,605,739**. It arises from the multiplicity-three Guruswami–Sudan/correlated-agreement machinery because candidate tuples may depend on gamma. The present three point-claim rows expose only 87 scalar functional values. They do not determine 29 component polynomials of degree up to 1,023/1,024, and the current theorem still has the quantifier shape

```text
for every gamma, there exists an accepting candidate tuple
```

rather than

```text
there exists one pre-gamma tuple used for every gamma.
```

Swapping those quantifiers without a transcript/source theorem is invalid.  A second, subtler invalid inference was also found: the Rust no-new-tree verifier checks the gamma dot of each 29-value public vector, not component-wise equality between that vector and an extracted candidate tuple.  A fixed 29-vector supported in its first two lanes can be chosen to match independently prescribed scalar values at two distinct gammas, so parser replay of the public bytes alone cannot select one tuple.

The correct bound does not need that false inference.  For each fixed tuple whose complete two-point fingerprint differs from the public vectors, at least one gamma-dot discrepancy is a nonzero degree-at-most-28 polynomial.  It therefore passes both scalar checks for at most 28 nonzero gammas.  Union over the actual at-most-100 tuple family gives **2,800** bad gammas without assuming an exact full-fingerprint match; with a known matching anchor, the 99 alternatives give **2,772**.  Lean proves both bounds and the constructive countermodel.  The ledger conservatively uses 2,800.

## 9. Two-point DEEP mathematics and the corrected circle construction

An early prototype used `(t-t0)(t-t1)` in a stereographic parameter. Adversarial inspection showed that this is not the degree-one circle-coordinate factor expected by the existing fold basis. The exact identity is

```text
L(z(t)) = 4*(t1-t0)*(t-t0)*(t-t1) /
          ((1+t0^2)*(1+t1^2)*(1+t^2)),
```

where the correct affine chord is

```text
L(x,y) = x0*y1 - y0*x1 + (y0-y1)*x + (x1-x0)*y.
```

The implementation was replaced with this chord and an affine interpolant using x when `x0 != x1`, otherwise y. Lean proves the rational-circle identity and nonvanishing away from the two OOD points. This correction also removes the need for 88 stereographic inversions: the optimized path uses one batch inversion for all 88 chord denominators.

Established abstract facts include:

- the rational circle parameterization lies on the circle and is injective on its finite chart;
- two-point interpolation is correct at both points;
- the affine chord vanishes at the two intended points and is nonzero at a different valid chart point;
- batching then interpolating/quotienting equals quotienting components then batching;
- the authenticated C1 M31 values are embedded canonically into QM31 while the three C2 components remain native QM31;
- ordinary univariate polynomial division by the two-root zerofier drops degree by two;
- the no-new-tree quotient is computable entirely from existing authenticated C1/C2 openings and the public vectors.

The continuation establishes the previously missing deployed circle-code facts:

- in the distinct-x branch, multiplying the residual pair by the conjugate chord produces two polynomials divisible by `(X-x0)(X-x1)`;
- the chord norm is exactly `(u^2+v^2)(X-x0)(X-x1)`, with the rational-map scalar proved nonzero for distinct secure parameters;
- division constructs a quotient pair of degrees at most `(511,510)`;
- in the equal-x branch, distinctness forces distinct y-coordinates and both residual components carry the linear factor `X-x0`, giving degrees at most `(510,510)`;
- pair multiplication evaluates to multiplication by the affine chord on `x^2+y^2=1`;
- every resulting pair has an exact 1,024-entry natural-basis message representative; and
- the complete width-29 gamma-batched adaptive quotient therefore lies in the deployed initial encoder without a new commitment tree.

The existing `v5_circle_fold_encoder0_commutes` theorem applies to that quotient message. What remains is source translation/integration of the V8 arithmetic and the restoration-wide transcript theorem, not the circle algebra itself.

## 10. Candidate separation and fixed pre-gamma tuple

The actual repository list is one joint list of at most **100** width-29 tuples, not 29 independent lists of cap 112. The cleared component degree bound used by the exact development is 1,024. For ordered distinct secure parameters, Lean proves:

```text
family two-point collision cardinality <= 100^2 * 1024^2
                                      = 10,485,760,000.
```

With secure parameter space `P^4 - P^2`, this contributes the exact sequential term

```text
10,485,760,000 /
((P^4-P^2) * (P^4-P^2-1)), P = 2^31-1,
```

which reduces to the JSON ledger's `625 / 26959946566717012180476293028281510290033389227972900691767591960832`, or 214.7122876151 bits.

Outside that collision event, equal two component-evaluation vectors select the same tuple. For one fixed tuple whose fingerprint differs from the proof-carried public vectors, Lean proves the two-scalar match set has cardinality at most **28**.  The family-wide release bound is **100*28 = 2,800**, not 28.

The initial source obligation used the legacy `RestoredK14BranchProvider`,
which requires a real coherent fallback extraction even for unavailable
challenges. That is not a causal pre-gamma interface: any such extraction is
post-gamma evidence. The V8 proof now uses only the partial provider it
actually consumes:

```lean
structure PartialRestoredK14BranchProvider
    (decoder : ExactDecoderInstantiation QM31Exact)
    (binding : InitialProjectionBinding decoder)
    (words : ExtractedWords) where
  branch : (gamma : QM31Exact) ->
    Option (RestoredK14Branch decoder binding words gamma)

structure ExactCompilerPreGammaTupleObligation
    (sourceFamily : RestoredSelectedBranchProvider decoder words)
    (componentPrefix : V8TwoPointComponentPrefix) where
  k14Family : PartialRestoredK14BranchProvider decoder binding words
  sourceRefinement :
    RestoredK14ProviderRefinesK13Provider sourceFamily k14Family
  prefixReplay :
    RestoredK14ProviderMatchesTwoPointPrefix k14Family componentPrefix
```

`V8A100SchedulerNativeK14Provider.lean` now constructs that partial family by
running the existing total K1.3/K1.4 classifiers on every proof returned by
the whole scheduler-native routed replay. Rejecting, malformed, zero-gamma,
K1.3-failing and width-29-failing branches map to `none`; no fallback or
cross-gamma premise is supplied by a caller. It also constructs the K1.3 view
of precisely those K1.4-successful branches and proves the refinement
definitionally.

The stronger `RestoredK14ProviderMatchesTwoPointPrefix` structure proves the
ideal full-vector result conditionally, but the actual verifier cannot supply
that field from scalar checks.  `V8A100ScalarFingerprintGammaBound.lean`
provides the correct replacement: outside the explicit at-most-2,800 gamma
set, any candidate passing both scalar checks has the complete public
fingerprint; outside the two-point collision event, two such candidates are
equal.  The source-connected release theorem must compose that result with
the partial K1.4 replay.

That composition cannot yet be stated against the production parsed type as
a field projection: `Tag73K12ParsedProof` contains V7 two-tree openings, one
gamma, a final message, a schedule, and `QuerySchedule 16 262144`; it has no
q22 schedule and no component OOD vectors. A separate 697-QM31 V8 raw/parsed
message, scalar-check classifier, and accepted quotient check must therefore
be translated before the new bound becomes a source theorem.

Three alternatives were examined:

1. reuse the three existing point claims — rejected by the quantifier/candidate countermodel above;
2. use raw transcript-coordinate occurrence — rejected because occurrence does not establish semantic replay, ordering, or cached/advance equality;
3. add a third OOD point — unnecessary for the abstract two-point uniqueness theorem and does not repair scalar-versus-component semantics or the missing V8 source parser.

## 11. New Lean results and axioms audit

All successful files were compiled individually before dependent work. No `sorry`, `admit`, new axiom, unproved opaque constant, or `unsafe` proof escape appears in the established modules.

| Module / result group | Key results | Focused build | `#print axioms` |
|---|---|---:|---|
| `V8A100DirectSchedule.lean` | q22 range/distinctness; ideal conditioned uniformity; exhaustion rejects; frontier ≤296; maximum fixture =296; body/account arithmetic | PASS 14.27 s; max RSS 5,732,073,472; zero swap | standard only |
| `V8A100TwoPointDeep.lean` | circle chart, interpolation, chord identity/nonvanishing, width-29 batching, ordinary degree drop | PASS 3.93 s; max RSS 5,721,030,656; zero swap | standard only |
| `V8A100CircleChordQuotient.lean` | chord-norm factorisation; distinct-x quadratic divisibility; equal-x linear divisibility; constructive circle-pair degree drops; pointwise chord multiplication | PASS 26.54 s; max RSS 4,851,236,864; zero swap | standard only |
| `V8A100CircleDeepCompatibility.lean` | exact rational-map instantiation; adaptive source branch; actual natural-basis quotient message; width-29 no-new-tree codeword theorem | PASS 6.47 s; max RSS 5,508,284,416; zero swap | standard only |
| `V8A100FixedTupleFingerprint.lean` | per-message/pair/family collision bounds, two-vector uniqueness, bad-gamma cardinality ≤28 | PASS 53.37 s; max RSS 4,538,695,680; zero swap | standard only |
| `K1/V8A100PreGammaTupleBinding.lean` | conditional restoration-wide full-vector theorem; fallback-free partial-provider interface | PASS 40.20 s; max RSS 4,232,740,864; zero swap | standard only |
| `K1/V8A100SchedulerNativeK14Provider.lean` | partial K1.4 provider from whole routed replay; derived K1.3 refinement; exact compiler specialization | PASS 23.85 s; max RSS 4,895,948,800; zero swap | standard only |
| `V8A100ScalarFingerprintGammaBound.lean` | scalar/full-vector countermodel; per-tuple ≤28; family ≤2,800; anchored ≤2,772; equality outside scalar/collision events | PASS 4.94 s; max RSS 5,348,524,032; zero swap | standard only |
| `V8A100HidingImageCriterion.lean` | exact uniform hiding from witness-image containment; deterministic postcomposition; Frobenius-graph hiding; ambient-surjectivity counterexample | PASS 31.32 s; max RSS 4,877,451,264; zero swap | standard only |
| `V8A100RawSecurityLedger.lean` | direct bridge from the fixed-family ≤2,800 theorem; q21≤2^-100; q22≤2^-104 and not≤2^-105; q23≤2^-105 | PASS 51.29 s; max RSS 4,030,398,464; zero swap | standard only |

“Standard only” means a subset of `propext`, `Classical.choice`, and `Quot.sound`, exactly as printed in the retained logs. It does not mean the conditional source assumptions were discharged; those are explicit structure parameters, not hidden axioms.

## 12. Rust direct-q22 and no-new-tree prototypes

The research path is separate from V7 and unreachable from any deployed instruction.

Implemented in `crates/aspis-core/src/v8_a100.rs`:

- V8-specific 32-byte profile binding `AV8A1001...`;
- q22 and depth-18 constants;
- direct bounded schedule with deterministic continuation;
- zero selector-stream and candidate counts in the profile;
- exact frontier derivation with a hard theorem-backed 296 bound;
- strict schedule range/duplicate validation;
- exact length and canonical packed-M31 parsing;
- source-tied compile-time wire assertions;
- deterministic KAT and maximum-frontier fixture.

Implemented in `crates/aspis-core/src/v8_deep.rs`:

- two canonical 29-QM31 vectors in the existing fixed field section;
- `zeta0; vector0; zeta1; vector1` absorption before gamma;
- distinct and secure-circle checks;
- a simple reference decoder/quotient path;
- a one-pass packed decoder and optimized quotient path;
- one shared gamma-power table and a three-output prepared dot;
- one batch inversion for 88 denominators;
- affine-chord zerofier and coordinate-adaptive interpolant;
- no quotient commitment, root, leaf, salt, query, or frontier.

Adversarial API review found that the original OOD-prefix helper absorbed
vector array A but did not retain it; a future caller could then construct a
challenge object containing array B and verify B against the wire.  The helper
now retains the exact absorbed vectors, the production-facing constructor
decodes them canonically from the V8 wire, and the only public challenge
constructor binds gamma to the retained points/vectors.  The challenge fields
are private, and a noncanonical deferred wire is rechecked before absorption.

The full release-filtered V8 core suite passed **16 tests** with one explicitly ignored host profile. It covers source-tied bytes, KAT continuation, V7/V8 domain separation, duplicate/range/exhaustion rejection, malformed lengths/frontier claims, transcript ordering, absorbed-vector retention, deferred-wire canonicality rechecking, malformed/duplicate/in-domain OOD inputs, zero denominators, reference/optimized agreement across generated cases, no-new-tree agreement, and wire mutation. Existing canonical parsers supply canonical M31/QM31 and trailing-data rejection. There is not yet a complete V8 prover, verifier instruction, Pool transaction, or Rust/Lean full-proof byte-level KAT.

## 13. Exact conditional raw-security ledger

No 35/31/34 proof-of-work factor divides any term. Work affects the explicit oracle resource envelope only.

The research envelope is:

```text
Q = 2^36
R = 259
verifier full-256 call cap = 1511
unified fresh exposures F = 17,867,064,344,738
global full-256 calls G = 35,665,408,818,844
visible honest work = 2^35 + 2^31 + 2^34 < Q
```

For q22/digest208/two OOD points, the exact reduced terms are:

| Event | Exact rational | Bits |
|---|---|---:|
| Query consistency | `332233934228956685743727459727502257791407791653047 / 14872013861920722188613414594812101323350365360984194543156711866198653246277652480` | 105.1420996194 |
| Algebraic nonzero-QM31 (`3+22+18+396430+2800`) | `19013 / 1012745137759265368428517155699425280` | 105.3929840068 |
| Two-point tuple collision | `625 / 26959946566717012180476293028281510290033389227972900691767591960832` | 214.7122876151 |
| K1.2 truncated Merkle | `159615994149495035122038437 / 411376139330301510538742295639337626245683966408394965837152256` | 120.9552643104 |
| Full-256 compiler/oracle | `796852148397184761592959563 / 115792089237316195423570985008687907853269984665640564039457584007913129639936` | 166.6355574681 |

The exact sum reduces to:

```text
123544701523935175020073869443526905862590612985139886722217520965615111796184994162384136291708221532905808968142797587018431284005853099210573865611233296039399159641718497651435293895518610721134405093
/
3004955569840591171834808569745081261900625163632461545750988555373443236893623232317267705677412870093632592596147630605517222307661579319682158216274883021244987586078588217147878956551485524691319979802487428641540413469043214778368
```

Its display value is **104.26208146248575 raw bits**. Lean proves it is at most `2^-104` and not at most `2^-105`.

The algebraic numerator was re-derived as:

```text
one fold 3
+ query batch 22
+ later alpha 18
+ K1.5 fixed family 396430
+ scalar-DEEP tuple-family gamma 2800
= 399273.
```

The K1.5 fixed-family subtotal is itself checked as
`30,500 + 292,800 + 73,100 + 1 + 1 + 2 + 24 + 2 = 396,430`, corresponding to the semantic, copy-lambda, copy-chi, mu-zero, inactive-chi, OOD-mix, relation-alpha, and kappa-point-row families. The former restoration-aware gamma residual is replaced by the conservative scalar-DEEP family cardinality 2,800; it is not also hidden in the 396,430 subtotal.

The K1.2 numerator is the unified fresh-exposure pair count plus `1,511 * (2*q)` verifier digest targets. The full-256 term is `F + C(F,2) + F*G`. Bounded q22 sampler exhaustion, secure-point rejection, duplicate second-point retry exhaustion, and zero-denominator detection all reject; they do not create a false-acceptance term. Their uniform/pointwise laws still need the literal source bridge noted above. Moving the OOD prefix also means every reused algebraic challenge bound must be re-instantiated at its new compiler coordinate; the conditional sum does not claim this source composition is already done.

The q22 maximum gamma cardinality compatible with the full envelope is exactly **15,905,625** for 100 bits and **176,985** for 104 bits. The conservative scalar-family result achieves 2,800 (or 2,772 with an exact anchor), so the corrected result still clears 104 bits. If the old 336,869,026,605,739 bound remained, neither target would be possible.

This ledger remains conditional because the current compiler theorem leaves Q and R symbolic, the exact event composition has not been rebuilt at the shifted transcript coordinates, and the V8 scalar-check/source composition is unconstructed. Thus “104.262 bits” is exact arithmetic under named assumptions, not a production soundness certificate.

## 14. Hiding and zero knowledge

The V8 public-view audit includes 22 fibres × four layer-zero openings, the
three existing semantic point-claim rows, both component-wise OOD rows,
fold/final disclosures, statement-specific values, and both pair and
pair-forest settlement layouts.  QM31 outputs are expanded into four M31
coordinates; an OOD value is not counted as one base-field constraint.

The original computational gate asked each C1 mask map to span an ambient
108-dimensional raw target.  That universal statement is rigorously false.
For a legal secure parameter `t0`, choose the distinct secure conjugate
`t1 = t0^P`.  Every M31-coefficient C1 polynomial then obeys

```text
f(zeta1) = f(zeta0)^P,
```

so the legal OOD rows lie on a Frobenius graph.  Exhaustive construction of all
1,024 natural-basis rows and optimized exact elimination report rank **104**,
not 108, for column zero in both layouts.  The pair replay passed in 21.41 s
with 553,762,816 bytes max RSS; pair-forest passed in 19.35 s with 606,928,896
bytes; both used zero swap.  The probability that the second distinct uniform
secure draw is one of the first point's three other Frobenius conjugates is

```text
3 / 21267647892944572732387174255555510271
```

or 122.41503749659161 bits.  Rejecting this orbit would add completeness loss
and would not classify all possible functional coincidences.

This is not a zero-knowledge counterexample: honest physical witnesses and
legal masks share the same Frobenius relation.  Lean proves the correct exact
criterion—schedule-wise image containment—and proves that it implies equality
of translated output distributions and survives arbitrary deterministic
postprocessing:

```lean
LinearMap.range witnessView ≤ LinearMap.range maskView
```

It also proves perfect hiding on the conjugate Frobenius graph despite failure
of ambient surjectivity.  The remaining source theorem is precisely:

```lean
∀ layout ∈ {pair, pairForest}, ∀ s,
  ValidV8Schedule s →
  LinearMap.range (completeSameStatementWitnessView layout s) ≤
    LinearMap.range (completeMaskView layout s)
```

A further focused source probe checked the first stronger subgate on the legal
conjugate fixture.  For each of the state-only model's 16 C1 mask columns, all
1,022 conservative physical semantic basis directions lie in the exact
relation-free mask span for both layouts, even though the ambient rank is
104/108.  The cached optimized run passed in 1.82 s (0.30 s test), used
121,913,344 bytes max RSS, and zero swap.  This is finite-field evidence for
one schedule, not a universal proof.

The universal Lean bridge cannot honestly be stated against existing
translations: exact repository search found no Lean/Aeneas definitions for
the q22 row public maps, `c1_raw_difference`, pair-forest mask inventory, or
the mask-balancing application.  Pair-forest is connected to the actual prover
mask path; `PoolPairV1` is presently a host rank model with no corresponding
OneFold pair-tree mask application.  The precise first translation target is:

```lean
theorem v8_perC1_physical_range_le_mask_range
    (layout : V8PoolLayout)
    (schedule : StateOnlyTranscriptScheduleResult)
    (hSchedule : ValidV8A100Schedule schedule)
    (column : Fin 16) :
  LinearMap.range (perC1PhysicalView layout schedule column) ≤
    LinearMap.range (perC1MaskView layout schedule column)
```

That per-C1 theorem, H cancellation, mask-only/G coverage, and deterministic
postcomposition to the complete view remain unproved for every schedule.
Exact V8 hiding therefore remains **open**, and no mask enlargement is
justified by the 104-versus-108 ambient deficit alone.

## 15. Runtime and CU evidence

### Diagnostic host profile

Release host timings, which are not CU:

| Phase | Time |
|---|---:|
| OOD prefix and vector absorption | 8,578 ns |
| Gamma powers and two OOD dots | 2,420 ns |
| One one-pass query decode | 214 ns |
| All query circle points | 291 ns |
| Optimized full DEEP path | 30,057 ns |
| Reference full DEEP path | 287,712 ns |
| Optimized inversions | 1 |
| Reference inversions | 88 |

The optimized path is about 9.57× faster on this host, validating batch inversion, shared powers, and one-pass decoding as worthwhile shapes. It does not justify a 30–45k CU estimate.

### SBF gate

The local release script first failed correctly on Darwin/arm64.  A repository
learning file then revealed the Linux/x86_64 NUC.  In a task-owned remote
directory, zero-swap cgroup scopes built the V7 verifier and Pool programs with
platform-tools v1.48/Solana 2.3.0 and ran strict-work LiteSVM transactions:

| Shape | Total CU | Verifier CPI CU | TxV1 bytes | Max RSS | Result |
|---|---:|---:|---:|---:|---|
| V7 same-page withdrawal | 1,153,267 | 1,085,276 | 1,010 | 539,436 KiB | accepted |
| V7 rollover withdrawal | 1,218,981 | 1,084,747 | 1,043 | 541,352 KiB | accepted |

The fresh verifier ELF was 1,819,432 bytes and the Pool ELF 536,752 bytes.
Nothing used RPC, a public validator, deployment, signing, or live state.

The SBF analyzer first exposed a V8-specific blocker even though V7 itself
builds: `v8_deep_quotients_reference_wire` had an **11,904-byte** frame and
`v8_deep_quotients_optimized_wire` an **18,880-byte** frame, versus the SBF
**4,096-byte** limit.  Moving only the wide arrays to the heap still left
7,168-byte frames.  A research refactor then made the caller own the output,
generated each fibre's circle points on demand, streamed C1/C2 gamma dots, and
moved only the batch prefixes and q22 scratch to the heap.  The final reachable
probe frames are **2,176 bytes** for heap-batched and **2,112 bytes** for
pointwise quotienting; every function reachable from the default-off probe is
below 4,096 bytes.  The production convenience helper
`derive_v8_a100_ood_prefix_from_wire` remains unreachable from the probe and
still has a **4,736-byte** frame, which is the precise remaining stack-integration
obligation.

The capped Linux LiteSVM probes accepted the exact 39,934-byte maximum-frontier
wire shape and measured:

| Isolated probe | Total transaction CU | Program CU | Named region CU |
|---|---:|---:|---:|
| Heap-batched quotient, one inversion | 807,012 | 806,862 | 750,111 |
| Pointwise quotient, 88 inversions | 791,539 | 791,389 | 734,638 |
| Canonical parser only | 634,879 | 634,729 | 633,942 |

The pointwise result is 15,473 CU cheaper on the all-zero canonical fixture,
but that special denominator distribution does not establish that 88 general
inversions beat batch inversion.  The host property tests, rather than this CU
fixture, establish equality with the slow reference.  The three isolated totals
cannot be added or promoted to a complete-verifier estimate: the quotient
probes use deferred canonicality and their own entry/transcript setup, while the
parser uses a separate entry.  An earlier combined canonical-parse plus
heap-kernel probe reached the kernel with 723,486 CU remaining and exhausted
the 1.4M limit.  That rules out the straightforward combined probe shape, not
all integrated implementations.

Even after the stack-safe kernel, the repository lacks a complete V8 transcript
verifier, q22 Merkle/fold composition, pair-forest dispatch, honest prover
fixture, and V8-aware Pool grammar.  Therefore:

- worst measured V8 transaction CU: **not available**;
- compliance with 1.4M and preferred 1.35M: **unestablished**;
- isolated V8 parser and quotient CU: **measured**, with all probe-reachable
  frames stack-safe;
- complete V8 heap, CPI split, SHA count, and transaction account sizes:
  **unmeasured on SBF**;
- the profile cannot receive classification A or B.

The CPU-critical alternatives actually implemented and compared are batch
inversion versus pointwise inversion, shared gamma powers, streaming multi-output
dots, one-pass field decoding, and caller-owned output. Removing the candidate
scan is structural in the direct schedule. The measurement shows that the
kernel's approximately 735k--750k CU is now the engineering concern; stack
lifetime is closed for the isolated probe but not for the production helper.

## 16. Failure ledger and what each failure established

| Failure | Classification | Reduced cause | Alternatives attempted / outcome |
|---|---|---|---|
| Initial 608-byte query assumption | Incorrect assumption | C1 is 403, C2 is 186, salt is 32: total 621 | Derived from source constants; added compile-time assertions; added exact audit tests. |
| q22 frontier conjecture might have been probabilistic | Potential false premise | Need deterministic max, not cap likelihood | Derived closed form; proved capacity/telescoping bound; constructed fixture attaining 296 in Rust and Lean. |
| Compact V7 schedule law unsuitable | Design mismatch | 64 candidate branches and frontier conditioning | Reused sampler directly once; retained exact continuation; made exhaustion reject; removed candidate/counter fields. |
| Existing point claims expected to imply degree-28 gamma bound | False inference | Candidate tuple remains gamma-dependent | Inspected actual hypotheses; built fixed-list toy/pair/family ladder; isolated source-wide fixed tuple obligation. |
| Full public component vectors expected to imply full candidate fingerprints | False inference / countermodel | Rust checks only two gamma dots; a two-lane vector can interpolate arbitrary scalars at two gammas | Proved the countermodel; bounded every nonmatching tuple by 28 gammas; unioned the at-most-100 family to 2,800, with an anchored 2,772 refinement. |
| Raw coordinate occurrence as source binding | Type/semantics mismatch | Does not cover semantic replay or cached/advance paths | Compared scheduler/compiler interfaces; constructed the fallback-free K1.4 family from the executable routed replay; retained the V8 prefix replay as one explicit parser/source obligation. |
| Legacy K1.4 fallback provider as pre-gamma family | Type-design problem | Required a genuine coherent extraction for an unavailable branch, which is post-gamma evidence | Introduced the strictly weaker partial provider actually consumed by V8; adapted legacy providers; constructed the partial provider directly from replay/classification. |
| Focused pre-gamma rebuild initially missed/failed V7 oleans | Source/API and cache mismatch | The research branch source, newer main dependency cache, and an independently rebuilding main cache were not one coherent revision | Tried the research predecessor, matching main source, and a clean activation-worktree olean/cache overlay; retained exact errors and did not count declarations reporting `sorryAx`; reran only the focused V8 modules once the import interface was coherent. |
| Third OOD point as easy repair | Dominated alternative | Two points already give abstract uniqueness; source gap is replay, not collision | Quantified +449 bytes; retained same conservative ledger; rejected as default. |
| Stereographic `(t-t0)(t-t1)` quotient | Mathematical/source-model mismatch | Not the degree-one affine circle factor | Derived chord identity; replaced Rust and Lean model with affine chord; retained ordinary parameter result only as a non-release lemma. |
| First coordinate-ring factor proof | Incorrect proof certificate | Direct polynomial linear combination did not match the required ideal identity | Tried direct combination and normalization; succeeded by proving the linear and constant coefficient identities separately, then normalizing symbolically. |
| Concrete residual bridge timed out at `whnf` | Proof-shape/resource pathology | Elaboration unfolded the 512-entry natural-basis constructor in direct message-specific statements | Tried the existing max-recursion precedent and explicit rewrites; then replaced them with typed generic residual lemmas and a late concrete instantiation. No heartbeat increase was used. |
| Equal-x Rust fixture initially found no point | Incorrect geometric assumption in test | `(t,-1/t)` has opposite x in this chart; equal x is `(t,-t)` | Reduced to the rational formulas, corrected only the adversarial fixture, and passed the y-interpolation/chord-root test plus the full V8 release suite. |
| First Lean chord proof | Missing local algebraic lemma | Tactic could not discharge `4 != 0` cleanly | Factored `4 = 2*2` and used symbolic nonzero multiplication; final file compiles without `sorryAx`. |
| First exact ledger build expanded huge `Nat.choose` | Resource pathology | Broad normalization unfolded a huge recurrence | Stopped near policy limit; used `Nat.choose_two_right`; introduced named sparse literal and exact bridge theorem; focused rebuild passed in 10.69 s. |
| Exact V7 capstone local replay | Environment/cache limitation | Required `.olean` objects absent; cold replay violates local memory policy | Checked research and main caches; used retained exact build evidence; did not launch uncapped rebuild. |
| Rust prefix absorbed A but challenge object could carry B | API causality defect | Prefix did not retain the proof-carried vectors and challenge fields were public | Retained canonical wire vectors in the prefix; made challenge construction private/prefix-owned; added A≠B/noncanonical-wire regression tests. |
| Local SBF replay | Environment limitation resolved | Release script requires Linux x86_64 | Captured fail-fast output, found repository-documented NUC, then reproduced fresh V7 SBF and strict-work LiteSVM baselines under capped zero-swap scopes. |
| Reachable V8 quotient on SBF | Resource/implementation-shape failure, then partial success | Reference/optimized frames were 11,904/18,880 bytes; heap-only was 7,168; all exceeded 4,096 | Caller-owned outputs plus streamed fibre/gamma work reached 2,176/2,112-byte frames and accepted isolated CU probes; the unused production helper remains 4,736 bytes. |
| Combined canonical parser plus heap DEEP probe | Resource exhaustion | Straight-line isolated composition reached the kernel with 723,486 CU left and exceeded 1.4M | Split the phases, measured parser and both kernels independently, compared pointwise versus batch inversion, and retained the failure without claiming a complete transaction bound. |
| Ambient-rank hiding theorem | False conjecture | Legal Frobenius-conjugate OOD pair forces rank 104, not 108 | Produced both-layout counterexamples; proved the legal-image criterion and conjugate-graph hiding; passed all 1,022 per-column physical directions on the fixture; isolated the absent row-map/mask translations blocking the universal theorem. |
| Workspace-wide formatting check | Pre-existing source mismatch | `cargo fmt --all -- --check` reports diffs in untouched V7/statement files | Ran standalone `rustfmt --edition 2021 --check` on all changed V8/audit Rust sources successfully; did not rewrite unrelated base files. |

## 17. Requirements matrix

| Requirement | Result |
|---|---|
| ≥100 raw bits without PoW | Conditional exact ledger: yes; source-complete theorem: no. |
| Prefer ≥104 raw bits | Corrected conditional q22/208 result: 104.2620814625; production theorem open. |
| Direct q22 over `2^18` | Implemented/tested; ideal sampler theorem instantiated; literal source correspondence incomplete. |
| No 64-candidate frontier search | Implemented in isolated V8 path. |
| Two component-wise pre-gamma vectors | Implemented and transcript-tested; scalar/full-vector distinction formally repaired. |
| No extra Merkle tree | Prototype derives all quotient values from existing authenticated openings. |
| Roughly 40 KB body | Exact maximum 39,934 bytes. |
| One transaction <1.4M CU | Not measured for a complete V8 verifier; the straightforward combined parser/DEEP probe exhausted 1.4M. |
| Preferred ≤1.35M CU | Unestablished; isolated pointwise kernel 791,539 CU and parser 634,879 CU cannot be summed as a transaction result. |
| Exact q22 hiding | Open; ambient-surjectivity target refuted, exact legal-image criterion proved, source containment missing. |
| Lean connected to actual Rust verifier | Circle quotient, adaptive branch, width-29 message membership, existing fold representation, fallback-free restoration replay, and scalar-family gamma bound exist; exact production V8 parser/transcript/scalar-check translation remains open. |

## 18. Best profile and go/no-go decision

Best profile:

```text
q = 22
digest = 26 bytes / 208 bits
OOD points = 2, component-wise and sequentially bound before gamma
mask = unchanged dimensions, provisionally
maximum frontier/tree = 296
maximum proof body = 39,934 bytes
complete pair-verifier account = 40,662 bytes
conditional raw security = 104.26208146248575 bits
```

Why not q21: it reaches only 100.318 conditional bits, below the preferred target and with a much smaller theorem margin. Why not q23: it costs another 1,245 body bytes and more Merkle/fold work for about 1.07 bits; q22 already crosses 104. Why not q24: algebraic terms dominate and the gain over q23 is only about 0.059 bits. Why not wider digest: K1.2 already has 120.955 bits and the total barely changes. Why not three OOD points: +449 bytes without a demonstrated need or a credited ledger improvement.

**Go/no-go:** no-go for production release now; go for one more tightly scoped research/integration tranche. The candidate is not ruled out under the stated constraints.

## 19. Remaining exact gaps

1. Implement a feature-gated V8 verifier instruction and prover KAT without changing V7.
2. Translate/refine the V8 parser, direct sampler, prefix replay, gamma dots, chord quotient, authentication, and terminal result into the source pipeline.
3. Extend the production parsed-proof/source type with the q22 schedule and two component vectors, then connect its two scalar gamma-dot acceptance checks to `fixedWidth29_nonmatching_scalar_gamma_card_le_2800` across fresh, cached, and advance continuations.  Do not require the false unconditional full-vector prefix equality.
4. Reassemble K1.2–K1.6 at the shifted challenge coordinates and instantiate Q/R from actual compiler resources.
5. Prove schedule-wise legal witness-image containment in the mask image for pair and pair-forest layouts, including Frobenius-conjugate and other functional-equality cases.
6. Refactor the remaining 4,736-byte production prefix-from-wire helper, fuse canonical parsing with streaming quotient preparation without a duplicate scan, and integrate an honest V8 verifier/prover fixture.  Then run verifier-only, same-page, rollover, typical/max frontier, and strict-work transactions on the capped Linux host.
7. Produce complete cross-language byte-level KATs and a final capstone/axioms replay.

## 20. Most valuable next task

The highest-value theorem task is **a translated V8 parsed message and accepting scalar-check classifier composed with the proved at-most-2,800 gamma event** for the exact partial provider.  The highest-value hiding task is the concrete legal-image-containment theorem, not another ambient-rank run.  The highest-value engineering task is to fuse canonical parsing with the now-stack-safe streaming quotient path and refactor the 4,736-byte production wrapper, then integrate an honest V8 transcript/Merkle/prover fixture.  Only that path can produce a decisive full-transaction CU result.

## Reproduction commands

Run from the research worktree. The machine-readable output is deterministic; the displayed timing/RSS varies by host.

### Exact arithmetic and Rust tests

```bash
cargo run --locked --release -p aspis-xtask --bin v8_a100_parameter_audit -- \
  --write results/v8-a100-q22/parameter-sweep.json

cargo test --locked -p aspis-core v8_ -- --nocapture
cargo test --locked --release -p aspis-core v8_ -- --nocapture
cargo test --locked -p aspis-core v7 -- --nocapture

/usr/bin/time -l cargo test --locked --release -p aspis-prover v7 -- --nocapture

cargo test --locked --release -p aspis-core \
  v8_deep::tests::host_profile_reference_and_optimized_deep_phases \
  -- --exact --ignored --nocapture
```

### Hiding witnesses

The two original generic witnesses are optimized, long-running jobs.  The
adversarial Frobenius tests below are focused exact counterexamples.

```bash
/usr/bin/time -l cargo test --locked --release -p aspis-prover \
  --test pool_pair_hiding_rank \
  v8_a100_q22_two_ood_pair_layout_rank_witness \
  -- --exact --ignored --nocapture

/usr/bin/time -l cargo test --locked --release -p aspis-core \
  --test v8_hiding_galois -- --nocapture

/usr/bin/time -l cargo test --locked --release -p aspis-prover \
  --test v8_hiding_galois_rank \
  v8_pair_ambient_rank_rejects_legal_frobenius_pair -- --exact --nocapture

/usr/bin/time -l cargo test --locked --release -p aspis-prover \
  --test v8_hiding_galois_rank \
  v8_pair_forest_ambient_rank_rejects_legal_frobenius_pair -- --exact --nocapture

/usr/bin/time -l cargo test --locked --release -p aspis-prover \
  --test pool_pair_hiding_rank \
  v8_a100_q22_two_ood_pair_forest_layout_rank_witness \
  -- --exact --ignored --nocapture
```

### Focused Lean builds and axioms

The following uses the existing main-worktree cache and compiles one changed leaf at a time, per repository policy:

```bash
export LEAN_PATH="$(cd /Users/dominic/ZK/AspisFormal && lake env printenv LEAN_PATH)"
export LEAN_BIN=/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean

/usr/bin/time -l "$LEAN_BIN" -o /tmp/V8A100DirectSchedule.olean \
  AspisFormal/AspisFormal/V8A100DirectSchedule.lean
/usr/bin/time -l "$LEAN_BIN" \
  -o /Users/dominic/ZK/AspisFormal/.lake/build/lib/lean/AspisFormal/V8A100TwoPointDeep.olean \
  AspisFormal/AspisFormal/V8A100TwoPointDeep.lean
/usr/bin/time -l "$LEAN_BIN" \
  -o /Users/dominic/ZK/AspisFormal/.lake/build/lib/lean/AspisFormal/V8A100CircleChordQuotient.olean \
  AspisFormal/AspisFormal/V8A100CircleChordQuotient.lean
/usr/bin/time -l "$LEAN_BIN" \
  AspisFormal/AspisFormal/V8A100CircleDeepCompatibility.lean
/usr/bin/time -l "$LEAN_BIN" -o /tmp/V8A100FixedTupleFingerprint.olean \
  AspisFormal/AspisFormal/V8A100FixedTupleFingerprint.lean
/usr/bin/time -l "$LEAN_BIN" -o /tmp/V8A100PreGammaTupleBinding.olean \
  AspisFormal/AspisFormal/K1/V8A100PreGammaTupleBinding.lean
/usr/bin/time -l "$LEAN_BIN" -o /tmp/V8A100SchedulerNativeK14Provider.olean \
  AspisFormal/AspisFormal/K1/V8A100SchedulerNativeK14Provider.lean
/usr/bin/time -l "$LEAN_BIN" -o /tmp/V8A100ScalarFingerprintGammaBound.olean \
  AspisFormal/AspisFormal/V8A100ScalarFingerprintGammaBound.lean
/usr/bin/time -l "$LEAN_BIN" -o /tmp/V8A100HidingImageCriterion.olean \
  AspisFormal/AspisFormal/V8A100HidingImageCriterion.lean
/usr/bin/time -l "$LEAN_BIN" -o /tmp/V8A100RawSecurityLedger.olean \
  AspisFormal/AspisFormal/V8A100RawSecurityLedger.lean
```

Each module contains its own `#print axioms` commands. The committed logs preserve the exact output, wall time, RSS, swap, and exit result.

### Exact SBF evidence

The Darwin command remains a useful fail-fast check:

```bash
scripts/v7_one_tx_release_replay.sh build \
  results/v8-a100-q22/forbidden-darwin-sbf-attempt
```

The complete Linux V7 commands are copied verbatim in
`results/v8-a100-q22/sbf-linux-baseline-20260907.md`.  The stack-safe V8 probe
can first be checked on the host with:

```bash
cargo test --locked -p aspis-core \
  no_new_tree_wire_path_matches_slow_reference
cargo check --locked -p aspis-verifier --no-default-features \
  --features v8-deep-cu-probe,no-entrypoint
```

The exact bounded Linux `cargo-build-sbf`, `llvm-readobj --stack-sizes`, and
LiteSVM harness commands, along with the ELF hash, are in
`results/v8-a100-q22/sbf-stack-and-cu-20260907.md`.  There is still no
legitimate complete V8 withdrawal command until the full verifier and honest
fixture exist.

### Final artifact checks

```bash
audit_tmp=$(mktemp /tmp/v8-audit.XXXXXX)
cargo run --locked --release -p aspis-xtask --bin v8_a100_parameter_audit -- \
  --write "$audit_tmp"
cmp "$audit_tmp" results/v8-a100-q22/parameter-sweep.json
shasum -a 256 "$audit_tmp" results/v8-a100-q22/parameter-sweep.json

rustfmt --edition 2021 --check \
  crates/aspis-core/src/v8_a100.rs \
  crates/aspis-core/src/v8_deep.rs \
  xtask/src/bin/v8_a100_parameter_audit.rs

xmllint --html --noout \
  docs/reviews/v8_a100_q22_production_readiness.html
git diff --check
```

The regenerated JSON matched byte-for-byte at SHA-256
`4c6c90afed8f045afb08dfe15fa80fbe6ccf2ebd1a2008c85e2b63437c3bca63`.

## Evidence index

- `xtask/src/bin/v8_a100_parameter_audit.rs` — exact arithmetic, frontier expectation, sweep, and source assertions.
- `results/v8-a100-q22/parameter-sweep.json` — exact rationals and all q/digest/OOD profiles.
- `crates/aspis-core/src/v8_a100.rs` — isolated direct q22 wire/profile/sampler.
- `crates/aspis-core/src/v8_deep.rs` — reference and optimized corrected chord quotient.
- `AspisFormal/AspisFormal/V8A100DirectSchedule.lean` — q22 sampler/frontier/body results.
- `AspisFormal/AspisFormal/V8A100TwoPointDeep.lean` — interpolation/chord/batching results.
- `AspisFormal/AspisFormal/V8A100CircleChordQuotient.lean` — coordinate-ring chord factorisation, both secant cases, and exact degree drops.
- `AspisFormal/AspisFormal/V8A100CircleDeepCompatibility.lean` — adaptive rational-map instantiation and exact width-29 natural-basis quotient message.
- `AspisFormal/AspisFormal/V8A100FixedTupleFingerprint.lean` — collision and gamma-cardinality results.
- `AspisFormal/AspisFormal/V8A100ScalarFingerprintGammaBound.lean` — scalar/full-vector countermodel and 2,800/2,772 family bounds.
- `AspisFormal/AspisFormal/V8A100HidingImageCriterion.lean` — exact legal-image hiding criterion and Frobenius-graph theorem.
- `AspisFormal/AspisFormal/K1/V8A100PreGammaTupleBinding.lean` — exact source obligation and conditional restored theorem.
- `AspisFormal/AspisFormal/K1/V8A100SchedulerNativeK14Provider.lean` — exact fallback-free K1.4 family and K1.3 refinement from the routed compiler replay.
- `AspisFormal/AspisFormal/V8A100RawSecurityLedger.lean` — exact conditional ledger inequalities.
- `results/v8-a100-q22/hiding-rank-witnesses.json` — concrete pair/pair-forest ranks.
- `results/v8-a100-q22/hiding-galois-counterexample-20260907.json` — exact pair/pair-forest ambient-rank counterexample, probability, resource and axioms evidence.
- `results/v8-a100-q22/hiding-per-c1-source-gap-20260907.json` — 1,022-direction-per-column containment fixture and exact missing translation boundary.
- `results/v8-a100-q22/host-deep-profile.json` — diagnostic non-CU timings.
- `results/v8-a100-q22/sbf-environment-gate.txt` — exact final-SBF host gate.
- `results/v8-a100-q22/sbf-linux-baseline-20260907.{md,json}` — fresh V7 SBF/LiteSVM baseline and V8 stack-frame gate.
- `results/v8-a100-q22/sbf-stack-and-cu-20260907.md` — stack refactor ladder, exact reachable frames, commands, and isolated CU interpretation.
- `results/v8-a100-q22/sbf-deep-cu-current-20260907.json` — machine-readable accepted parser/heap/pointwise LiteSVM probes.
- `results/v8-a100-q22/sbf-deep-probe-harness/` — pinned default-off LiteSVM probe harness.
- `results/v8-a100-q22/lean-pregamma-k14-provider-20260907.md` — focused provider builds and complete cache/source failure ladder.
- `results/v8-a100-q22/scalar-fingerprint-prefix-evidence-20260907.md` — scalar countermodel/cardinality proof and Rust causality API replay.
- `results/v8-a100-q22/circle-deep-compatibility-20260907.txt` — focused Lean/Rust evidence and resolved failure record for the circle-code gate.
- `results/v8-a100-q22/*.log` — focused Rust/Lean baselines and axioms output.
- `docs/reviews/v8_a100_q22_production_readiness.html` — structured production-readiness review.
- `.superstack/build-context.md` — review handoff and exact fixes.
