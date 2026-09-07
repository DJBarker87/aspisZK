# V8-A100 direct-q22 two-point-DEEP feasibility investigation

Date: 2026-09-07
Classification: **C — promising but not yet established**

## Executive verdict

The best profile found is still the proposed **q22, 26-byte digest, two component-wise OOD points** profile. It has an exact maximum proof body of **39,934 bytes** and a complete pair-verifier account size of **40,662 bytes**. Under the explicitly named `Q = 2^36`, `R = 259`, and 1,511-verifier-call research resource envelope, the exact rational raw-error ledger is **104.26666237024358 bits** without crediting proof of work. Lean proves that conditional ledger is at most `2^-104` and not at most `2^-105`.

That is not yet a production theorem. Four independent release gates remain open:

1. the exact compiler/source pipeline does not yet construct a restoration-wide K1.4 provider that replays the two OOD vectors for cached and advance continuations;
2. the affine-chord quotient has not yet been connected to the exact circle-code degree/fold representation;
3. the unchanged masking system has concrete q22/two-OOD nonzero-minor witnesses, but no theorem covering every legal schedule and OOD pair;
4. the V8 prototype is deliberately unreachable from a deployed instruction, and this Darwin/arm64 host cannot reproduce the repository's Linux/x86_64 final-SBF transaction harness, so there is no honest V8 transaction-CU number.

These are precise proof and integration obligations, not evidence of impossibility. The byte result and optimized host prototype are favorable, but neither substitutes for the missing universal proof or SBF run. Consequently this work does not claim A or B, and it does not classify the candidate as D.

## 1. Repository and base selection

| Item | Value |
|---|---|
| Original checkout | `/Users/dominic/ZK` |
| Research worktree | `/Users/dominic/ZK/.worktrees/ZK-v8-a100-q22-deep-feasibility` |
| Research branch | `research/v8-a100-q22-deep-feasibility` |
| Exact base | `87a1b80e34a14eefca0111aae54a4893e85ad0a2` |
| Base parents | `6971d0c18c12488695808790afa2cf025ef9526a`, `d42334b89de4ec3b18839580e9c17bec5b804a91` |
| Toolchains observed | Rust 1.93, Lean 4.32, Solana 2.3 |
| Research host | Darwin arm64 |

The base is the merge `merge: integrate cutoff-20 q16 publication policy [skip ci]`. Its first parent contains the advanced exact K1.2–K1.6 work, while its second parent contains the most recent relevant production V7 first-cap-203/cutoff-20 implementation and CU evidence available when the worktree was created. This avoided silently combining incompatible topic branches.

Relevant recent branches at selection/review included:

| Branch | Tip | Relevance |
|---|---:|---|
| `main` | later advanced to `4c91f97a` | Production/formal integration continued after the research base was selected; this branch was intentionally not rebased mid-investigation. |
| `integration/v7-cutoff20-main-20260902` | `4420d842` | Cutoff-20 integration. |
| `research/v7-first-cap203-scan-cu-fix-20260902` | `d42334b8` | Exact current-binary frontier/CU work and one parent of the selected merge. |
| `research/v7-deposit-invariant-promotion-20260902` | `44602d36` | Pool transaction evidence. |
| `integration/v7-persisted-lane-closure-candidate-20260902` | `7e0f5aac` | Persisted-lane/source closure work. |
| `research/v7-persisted-lane-source-formal-closure-20260901` | `0ed3f0b1` | Exact Pool source formalization. |

The original checkout was not modified. Its current user-owned dirty work,
`AspisFormal/AspisFormal/K1/V7Tag73K13CorrectedAlphaGammaClosure.lean` and
untracked `AspisFormal/AspisFormal/K1/V7Tag73K13CorrectedAlphaPairEquality.lean`,
was preserved. All V8 changes were made in the separate worktree and on the
separate local branch. Nothing was pushed, merged, deployed, or published.

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

The source-derived `v7_onefold.rs` maximum body is **30,504 bytes**. A committed live report calls a 30,772-byte profile upload a “proof”, but does not resolve that artifact's grammar against the 30,504-byte `v7_onefold.rs` maximum. This report keeps those measurements distinct rather than silently treating 30,772 as this parser's body.

### Formal baseline

The selected base records the exact measured K1.6 capstone as a successful historical release replay: 2.87 s, 6,706,000 KiB maximum RSS, zero swap, with only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` axioms. A local targeted rebuild could not begin because the shared cache lacked `V7Tag73ExactRestoredConcreteK16Assembly.olean`; the main checkout's cache also lacked the exact restored and capstone objects. Starting a cold dependency rebuild locally would violate the repository's 8 GiB policy, and no configured Linux build host was discoverable. This is classified as a cache/environment limitation, not an unexplained theorem failure.

### Existing SBF/CU evidence at the selected source lineage

| Shape | CU | Status |
|---|---:|---|
| V7 withdrawal, same page | 1,136,135 | Frozen actual transaction evidence. |
| V7 withdrawal, rollover | 1,201,757 | Frozen actual transaction evidence. |
| Current-binary worst frontier 202, verifier only | 1,084,738 | Actual measurement in the cutoff-20 audit. |
| Current-binary worst frontier 202, rollover transaction | 1,218,972 | Actual measurement in the cutoff-20 audit. |
| Modeled frontier 203/cutoff 20 envelope | 1,299,084 | Calibrated envelope, not an executed exact maximum fixture and not promoted here to measured fact. |
| Finalized live rollover transaction | 1,196,956 total; 1,125,340 verifier | Actual finalized evidence; profile upload reported as 30,772 bytes. |

The local V8 work did not rerun those SBF measurements because the exact release script rejects Darwin/arm64 before building. The decisive environmental output is retained in `results/v8-a100-q22/sbf-environment-gate.txt`.

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
| 21 | 284 | 38,689 | 39,417 | 100.3614 | 100.3182 | Meets 100 only, with little theorem margin. |
| 22 | 296 | **39,934** | **40,662** | 105.1421 | **104.2667** | Best balance; only option near 40 KB that reaches 104. |
| 23 | 308 | 41,179 | 41,907 | 109.9230 | 105.3415 | Adds 1,245 bytes and query/Merkle work for 1.075 bits. |
| 24 | 320 | 42,424 | 43,152 | 114.7040 | 105.4007 | Dominated by algebraic terms; adds only 0.059 bits over q23. |

### Digest sweep for q22/two OOD points

| Digest | Body | Complete account | K1.2 bits | Conditional total bits |
|---:|---:|---:|---:|---:|
| 26 B / 208 bits | **39,934** | **40,662** | 120.9553 | **104.2666623702** |
| 27 B / 216 bits | 40,528 | 41,256 | 128.9553 | 104.2666759755 |
| 28 B / 224 bits | 41,122 | 41,850 | 136.9553 | 104.2666760287 |
| 32 B / 256 bits | 43,498 | 44,226 | 168.9553 | 104.2666760289 |

At the stated resource envelope, 208-bit Merkle digests are not the bottleneck. Widening by one byte costs 594 maximum-body bytes because both roots and both worst-case frontiers grow, but gains only 0.0000136 total bits. A 208-bit nominal birthday heuristic alone would be inadequate; the result above instead uses the exact K1.2 multi-target term. If the actual source resource envelope is later larger, this conclusion must be recomputed.

### Two versus three OOD points

A third 29-QM31 vector adds 449 packed bytes. At q22/digest26, body/account become 40,383/41,111 bytes. No mathematical failure found in the two-point fingerprint theorem requires it, and the conservative ledger deliberately gives it no extra credit. It is therefore dominated unless the source replay or universal-hiding proof reveals a specifically three-point obstruction.

### Mask sweep

The unchanged production mask dimensions passed concrete pair and pair-forest rank witnesses for q22/two OOD points. Because the universal theorem is open, “zero extra mask bytes” is a candidate, not a release fact. No justified minimum enlargement can be reported until the all-schedule/OOD rank theorem or a counterexample exists.

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

The order is coherent at the abstract transcript and Rust-prototype levels. It is not yet proved equivalent to all compiler restoration/fork paths. In particular, the existing scheduler model is fresh-only while the exact compiler supports cached and advance oracle queries. Raw history occurrence is weaker than semantic prefix replay and was not accepted as a substitute.

## 8. Why the old point claims do not imply a 28-gamma bound

The existing large bad-gamma cap is **336,869,026,605,739**. It arises from the multiplicity-three Guruswami–Sudan/correlated-agreement machinery because candidate tuples may depend on gamma. The present three point-claim rows expose only 87 scalar functional values. They do not determine 29 component polynomials of degree up to 1,023/1,024, and the current theorem still has the quantifier shape

```text
for every gamma, there exists an accepting candidate tuple
```

rather than

```text
there exists one pre-gamma tuple used for every gamma.
```

Swapping those quantifiers without a transcript/source theorem is invalid. Once one tuple is fixed before gamma, the difference of two 29-term gamma combinations is a nonzero polynomial of degree at most 28, so at most 28 gamma values are bad. The new work proves that final implication and isolates exactly what is needed to justify the quantifier swap in the executable compiler model.

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

Not established: the exact degree theorem in the deployed circle coordinate ring and compatibility of this chord quotient with the concrete fold/final representation. The ordinary polynomial degree-drop theorem cannot fill that gap.

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

Outside that collision event, equal two component-evaluation vectors select the same tuple. For a fixed unequal tuple pair, Lean proves the bad-gamma set has cardinality at most **28**.

The exact unclosed source conclusion is represented, without an axiom, by:

```lean
structure ExactCompilerPreGammaTupleObligation
    (sourceFamily : RestoredSelectedBranchProvider decoder words)
    (componentPrefix : V8TwoPointComponentPrefix) where
  k14Family : RestoredK14BranchProvider decoder binding words
  sourceRefinement :
    RestoredK14ProviderRefinesK13Provider sourceFamily k14Family
  prefixReplay :
    RestoredK14ProviderMatchesTwoPointPrefix k14Family componentPrefix
```

The required next source theorem must construct this structure with `sourceFamily` definitionally equal to `exactCompilerRestoredSelectedProvider` from one paused source execution, for fresh, cached, and advance continuations. Once supplied, `exact_obligation_restored_branches_use_one_fixed_tuple` proves that every available restored K1.4 branch uses the same component tuple outside the explicit collision event.

Three alternatives were examined:

1. reuse the three existing point claims — rejected by the quantifier/candidate countermodel above;
2. use raw transcript-coordinate occurrence — rejected because occurrence does not establish semantic replay, ordering, or cached/advance equality;
3. add a third OOD point — unnecessary for the abstract two-point uniqueness theorem and does not repair the missing source-provider construction.

## 11. New Lean results and axioms audit

All successful files were compiled individually before dependent work. No `sorry`, `admit`, new axiom, unproved opaque constant, or `unsafe` proof escape appears in the established modules.

| Module / result group | Key results | Focused build | `#print axioms` |
|---|---|---:|---|
| `V8A100DirectSchedule.lean` | q22 range/distinctness; ideal conditioned uniformity; exhaustion rejects; frontier ≤296; maximum fixture =296; body/account arithmetic | PASS 14.27 s; max RSS 5,732,073,472; zero swap | standard only |
| `V8A100TwoPointDeep.lean` | circle chart, interpolation, chord identity/nonvanishing, width-29 batching, ordinary degree drop | PASS 3.93 s; max RSS 5,721,030,656; zero swap | standard only |
| `V8A100FixedTupleFingerprint.lean` | per-message/pair/family collision bounds, two-vector uniqueness, bad-gamma cardinality ≤28 | PASS 53.37 s; max RSS 4,538,695,680; zero swap | standard only |
| `K1/V8A100PreGammaTupleBinding.lean` | conditional restoration-wide fixed-tuple theorem; exact missing source structure | PASS 18.06 s; max RSS 5,624,053,760; zero swap | standard only |
| `V8A100RawSecurityLedger.lean` | exact resource arithmetic; q21≤2^-100; q22≤2^-104 and not≤2^-105; q23≤2^-105 | PASS 10.69 s; max RSS 5,585,387,520; zero swap | standard only |

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

The targeted V8 suite passed 14 tests with one explicitly ignored host profile. It covers source-tied bytes, KAT continuation, V7/V8 domain separation, duplicate/range/exhaustion rejection, malformed lengths/frontier claims, transcript ordering, malformed/duplicate/in-domain OOD inputs, zero denominators, reference/optimized agreement across generated cases, no-new-tree agreement, and wire mutation. Existing canonical parsers supply canonical M31/QM31 and trailing-data rejection. There is not yet a complete V8 prover, verifier instruction, Pool transaction, or Rust/Lean full-proof byte-level KAT.

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
| Algebraic nonzero-QM31 (`3+22+18+396430+28`) | `18881 / 1012745137759265368428517155699425280` | 105.4030350184 |
| Two-point tuple collision | `625 / 26959946566717012180476293028281510290033389227972900691767591960832` | 214.7122876151 |
| K1.2 truncated Merkle | `159615994149495035122038437 / 411376139330301510538742295639337626245683966408394965837152256` | 120.9552643104 |
| Full-256 compiler/oracle | `796852148397184761592959563 / 115792089237316195423570985008687907853269984665640564039457584007913129639936` | 166.6355574681 |

The exact sum reduces to:

```text
615765195896271458593906838304356852203398514668424528842164826010176755601973808787893119011103058844753204820834875669872060284748312106251853025023021370790634828930410942839415074911059334145157922169
/
15024777849202955859174042848725406309503125818162307728754942776867216184468116161586338528387064350468162962980738153027586111538307896598410791081374415106224937930392941085739394782757427623456599899012437143207702067345216073891840
```

Its display value is **104.26666237024358 raw bits**. Lean proves it is at most `2^-104` and not at most `2^-105`.

The algebraic numerator was re-derived as:

```text
one fold 3
+ query batch 22
+ later alpha 18
+ K1.5 fixed family 396430
+ fixed-tuple gamma 28
= 396501.
```

The K1.5 fixed-family subtotal is itself checked as
`30,500 + 292,800 + 73,100 + 1 + 1 + 2 + 24 + 2 = 396,430`, corresponding to the semantic, copy-lambda, copy-chi, mu-zero, inactive-chi, OOD-mix, relation-alpha, and kappa-point-row families. The former restoration-aware gamma residual is the term replaced by the conditional fixed-tuple cardinality 28; it is not also hidden in the 396,430 subtotal.

The K1.2 numerator is the unified fresh-exposure pair count plus `1,511 * (2*q)` verifier digest targets. The full-256 term is `F + C(F,2) + F*G`. Bounded q22 sampler exhaustion, secure-point rejection, duplicate second-point retry exhaustion, and zero-denominator detection all reject; they do not create a false-acceptance term. Their uniform/pointwise laws still need the literal source bridge noted above. Moving the OOD prefix also means every reused algebraic challenge bound must be re-instantiated at its new compiler coordinate; the conditional sum does not claim this source composition is already done.

The q22 maximum gamma cardinality compatible with the full envelope is exactly **15,905,625** for 100 bits and **176,985** for 104 bits. The conditional fixed-tuple result achieves 28. If the old 336,869,026,605,739 bound remained, neither target would be possible.

This ledger remains conditional because the current compiler theorem leaves Q and R symbolic, the exact event composition has not been rebuilt at the shifted transcript coordinates, and the pre-gamma source obligation is unconstructed. Thus “104.266 bits” is exact arithmetic under named assumptions, not a production soundness certificate.

## 14. Hiding and zero knowledge

The V8 leakage map was extended with:

- 22 fibres × four layer-zero openings;
- the existing semantic point-claim rows;
- two component-wise circle-OOD rows;
- the existing fold/final/statement rows for pair and pair-forest variants;
- M31-to-QM31 coordinate expansion explicitly accounted over M31.

The concrete raw counts were:

```text
C1 raw M31 coordinates = 108
G/H raw M31 coordinates = 372
raw minor columns = 3180
masked sumcheck rank/declared = 1080/1084
joint PCS rank/declared = 4092/4464
ambient deficit = 372 M31 coordinates
```

Optimized release rank runs produced nonzero-minor witnesses for both layouts:

| Layout | Result | Wall | Max RSS | Swap |
|---|---|---:|---:|---:|
| Pair | PASS | 874.01 s | 1,614,856,192 | 0 |
| Pair forest | PASS | 881.06 s | 1,467,301,888 | 0 |

Physical, legal, and helper coupled subspaces were contained in both witnesses. This is strong evidence that the unchanged mask may suffice for the tested maximum fixture/OOD pair. It is not the requested proof for every legal q22 schedule and secure distinct OOD pair. Duplicate/equality functional cases have not been universally classified. Exact zero knowledge therefore remains **open**, and no claim of minimum additional mask dimension is made.

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

The exact command attempted was:

```text
scripts/v7_one_tx_release_replay.sh build \
  results/v8-a100-q22/forbidden-darwin-sbf-attempt
```

It exited 1 with:

```text
FAIL: release SBF reproduction requires Linux x86_64; this host is Darwin arm64
```

No output directory, program artifact, transaction, deployment, or live state was created. No configured build-host destination was present in the repository. Even on Linux, the current V8 module is not connected to an SBF instruction or Pool settlement route, so measuring the requested V8 verifier/same-page/rollover shapes first requires a feature-gated integration.

Therefore:

- worst measured V8 transaction CU: **not available**;
- compliance with 1.4M and preferred 1.35M: **unestablished**;
- stack, heap, CPI split, SHA count, and V8 transaction account sizes: **unmeasured on SBF**;
- the profile cannot receive classification A or B.

The two critical-path optimizations already implemented and compared are batch inversion (88 to one inversion) and shared gamma powers/multi-output dots plus one-pass decoding. Removing the candidate scan is structural in the direct schedule. Further CU work before source coherence would be premature, but a Linux feature-gated SBF probe is the next empirical gate.

## 16. Failure ledger and what each failure established

| Failure | Classification | Reduced cause | Alternatives attempted / outcome |
|---|---|---|---|
| Initial 608-byte query assumption | Incorrect assumption | C1 is 403, C2 is 186, salt is 32: total 621 | Derived from source constants; added compile-time assertions; added exact audit tests. |
| q22 frontier conjecture might have been probabilistic | Potential false premise | Need deterministic max, not cap likelihood | Derived closed form; proved capacity/telescoping bound; constructed fixture attaining 296 in Rust and Lean. |
| Compact V7 schedule law unsuitable | Design mismatch | 64 candidate branches and frontier conditioning | Reused sampler directly once; retained exact continuation; made exhaustion reject; removed candidate/counter fields. |
| Existing point claims expected to imply degree-28 gamma bound | False inference | Candidate tuple remains gamma-dependent | Inspected actual hypotheses; built fixed-list toy/pair/family ladder; isolated source-wide fixed tuple obligation. |
| Raw coordinate occurrence as source binding | Type/semantics mismatch | Does not cover semantic replay or cached/advance paths | Compared scheduler/compiler interfaces; added explicit K1.3 refinement and K1.4 prefix replay structure; did not smuggle it into the final claim. |
| Third OOD point as easy repair | Dominated alternative | Two points already give abstract uniqueness; source gap is replay, not collision | Quantified +449 bytes; retained same conservative ledger; rejected as default. |
| Stereographic `(t-t0)(t-t1)` quotient | Mathematical/source-model mismatch | Not the degree-one affine circle factor | Derived chord identity; replaced Rust and Lean model with affine chord; retained ordinary parameter result only as a non-release lemma. |
| First Lean chord proof | Missing local algebraic lemma | Tactic could not discharge `4 != 0` cleanly | Factored `4 = 2*2` and used symbolic nonzero multiplication; final file compiles without `sorryAx`. |
| First exact ledger build expanded huge `Nat.choose` | Resource pathology | Broad normalization unfolded a huge recurrence | Stopped near policy limit; used `Nat.choose_two_right`; introduced named sparse literal and exact bridge theorem; focused rebuild passed in 10.69 s. |
| Exact V7 capstone local replay | Environment/cache limitation | Required `.olean` objects absent; cold replay violates local memory policy | Checked research and main caches; used retained exact build evidence; did not launch uncapped rebuild. |
| SBF replay | Environment limitation | Release script requires Linux x86_64 | Captured exact fail-fast output; checked local tool availability and repository host configuration; kept host benchmark explicitly non-CU. |
| Universal V8 hiding | Missing theorem, not counterexample | Concrete nonzero minors do not quantify over every schedule/OOD pair | Ran pair and pair-forest optimized witnesses; expanded leakage rows and dimensions; recorded exact remaining universal statement. |
| Workspace-wide formatting check | Pre-existing source mismatch | `cargo fmt --all -- --check` reports diffs in untouched V7/statement files | Ran standalone `rustfmt --edition 2021 --check` on all changed V8/audit Rust sources successfully; did not rewrite unrelated base files. |

## 17. Requirements matrix

| Requirement | Result |
|---|---|
| ≥100 raw bits without PoW | Conditional exact ledger: yes; source-complete theorem: no. |
| Prefer ≥104 raw bits | Conditional q22/208 result: 104.2666623702; production theorem open. |
| Direct q22 over `2^18` | Implemented/tested; ideal sampler theorem instantiated; literal source correspondence incomplete. |
| No 64-candidate frontier search | Implemented in isolated V8 path. |
| Two component-wise pre-gamma vectors | Implemented and transcript-tested. |
| No extra Merkle tree | Prototype derives all quotient values from existing authenticated openings. |
| Roughly 40 KB body | Exact maximum 39,934 bytes. |
| One transaction <1.4M CU | Not measured for V8. |
| Preferred ≤1.35M CU | Not measured for V8. |
| Exact q22 hiding | Open; concrete witnesses only. |
| Lean connected to actual Rust verifier | Partial source-model reuse; exact production V8 verifier does not yet exist and restoration-wide bridge is open. |

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
conditional raw security = 104.26666237024358 bits
```

Why not q21: it reaches only 100.318 conditional bits, below the preferred target and with a much smaller theorem margin. Why not q23: it costs another 1,245 body bytes and more Merkle/fold work for about 1.075 bits; q22 already crosses 104. Why not q24: algebraic terms dominate and the gain over q23 is only about 0.059 bits. Why not wider digest: K1.2 already has 120.955 bits and the total barely changes. Why not three OOD points: +449 bytes without a demonstrated need or a credited ledger improvement.

**Go/no-go:** no-go for production release now; go for one more tightly scoped research/integration tranche. The candidate is not ruled out under the stated constraints.

## 19. Remaining exact gaps

1. Prove the circle-coordinate-ring divisibility/degree statement for the affine chord and connect it to the actual fold/final representation.
2. Implement a feature-gated V8 verifier instruction and prover KAT without changing V7.
3. Translate/refine the V8 parser, direct sampler, prefix replay, gamma dots, chord quotient, authentication, and terminal result into the source pipeline.
4. Construct `ExactCompilerPreGammaTupleObligation` from the actual paused compiler for fresh, cached, and advance continuations.
5. Reassemble K1.2–K1.6 at the shifted challenge coordinates and instantiate Q/R from actual compiler resources.
6. Prove universal hiding for every valid q22 schedule and distinct secure OOD pair, or produce a counterexample and compute the minimum mask enlargement.
7. On a capped Linux/x86_64 build host, run actual SBF verifier-only, same-page, rollover, typical/max frontier, and strict-work transactions, recording CU/stack/heap/CPI/SHA/inversion counters.
8. Produce complete cross-language byte-level KATs and a final capstone/axioms replay.

## 20. Most valuable next task

The highest-value next task is **the exact affine-chord circle-code bridge**, immediately followed by a feature-gated Linux SBF probe. The theorem should state that for two distinct secure off-domain circle points and a component polynomial in the actual initial circle-code representation, subtracting the coordinate-adaptive affine interpolant is divisible by their chord in the circle coordinate ring, with the precise degree drop needed by the existing fold/final verifier. This decides whether the mathematically corrected no-new-tree quotient is actually compatible with production folding before investing in broad Pool integration.

If that focused bridge succeeds, wire the already-tested V8 core into a research-only instruction and measure maximum-frontier rollover. If it fails with a counterexample, the current V8 construction can be ruled out or revised without paying the cost of a full compiler and Pool proof.

## Reproduction commands

Run from the research worktree. The machine-readable output is deterministic; the displayed timing/RSS varies by host.

### Exact arithmetic and Rust tests

```bash
cargo run --locked -p aspis-xtask --bin v8_a100_parameter_audit -- \
  --write results/v8-a100-q22/parameter-sweep.json

cargo test --locked -p aspis-core v8_ -- --nocapture
cargo test --locked -p aspis-core v7 -- --nocapture

/usr/bin/time -l cargo test --locked --release -p aspis-prover v7 -- --nocapture

cargo test --locked --release -p aspis-core \
  v8_deep::tests::host_profile_reference_and_optimized_deep_phases \
  -- --exact --ignored --nocapture
```

### Hiding witnesses

These are optimized, long-running jobs. On macOS they were run separately and never concurrently.

```bash
/usr/bin/time -l cargo test --locked --release -p aspis-prover \
  --test pool_pair_hiding_rank \
  v8_a100_q22_two_ood_pair_layout_rank_witness \
  -- --exact --ignored --nocapture

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
/usr/bin/time -l "$LEAN_BIN" -o /tmp/V8A100TwoPointDeep.olean \
  AspisFormal/AspisFormal/V8A100TwoPointDeep.lean
/usr/bin/time -l "$LEAN_BIN" -o /tmp/V8A100FixedTupleFingerprint.olean \
  AspisFormal/AspisFormal/V8A100FixedTupleFingerprint.lean
/usr/bin/time -l "$LEAN_BIN" -o /tmp/V8A100PreGammaTupleBinding.olean \
  AspisFormal/AspisFormal/K1/V8A100PreGammaTupleBinding.lean
/usr/bin/time -l "$LEAN_BIN" -o /tmp/V8A100RawSecurityLedger.olean \
  AspisFormal/AspisFormal/V8A100RawSecurityLedger.lean
```

Each module contains its own `#print axioms` commands. The committed logs preserve the exact output, wall time, RSS, swap, and exit result.

### Exact SBF environment gate

On this host this is expected to fail fast without writing an artifact:

```bash
scripts/v7_one_tx_release_replay.sh build \
  results/v8-a100-q22/forbidden-darwin-sbf-attempt
```

The decisive V8 CU run must instead occur on the repository's capped Linux/x86_64 build host after the feature-gated verifier/Pool route exists.

### Final artifact checks

```bash
audit_tmp=$(mktemp /tmp/v8-audit.XXXXXX)
cargo run --locked -p aspis-xtask --bin v8_a100_parameter_audit -- \
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
`2202a801b6732b1b98808e5d4ecd6dae47ae69f78ee7bd61724bf3350958cf16`.

## Evidence index

- `xtask/src/bin/v8_a100_parameter_audit.rs` — exact arithmetic, frontier expectation, sweep, and source assertions.
- `results/v8-a100-q22/parameter-sweep.json` — exact rationals and all q/digest/OOD profiles.
- `crates/aspis-core/src/v8_a100.rs` — isolated direct q22 wire/profile/sampler.
- `crates/aspis-core/src/v8_deep.rs` — reference and optimized corrected chord quotient.
- `AspisFormal/AspisFormal/V8A100DirectSchedule.lean` — q22 sampler/frontier/body results.
- `AspisFormal/AspisFormal/V8A100TwoPointDeep.lean` — interpolation/chord/batching results.
- `AspisFormal/AspisFormal/V8A100FixedTupleFingerprint.lean` — collision and gamma-cardinality results.
- `AspisFormal/AspisFormal/K1/V8A100PreGammaTupleBinding.lean` — exact source obligation and conditional restored theorem.
- `AspisFormal/AspisFormal/V8A100RawSecurityLedger.lean` — exact conditional ledger inequalities.
- `results/v8-a100-q22/hiding-rank-witnesses.json` — concrete pair/pair-forest ranks.
- `results/v8-a100-q22/host-deep-profile.json` — diagnostic non-CU timings.
- `results/v8-a100-q22/sbf-environment-gate.txt` — exact final-SBF host gate.
- `results/v8-a100-q22/*.log` — focused Rust/Lean baselines and axioms output.
- `docs/reviews/v8_a100_q22_production_readiness.html` — structured production-readiness review.
- `.superstack/build-context.md` — review handoff and exact fixes.
