# Optimized relation: V7 algebra reuse and the remaining source interface

Research checkpoint: `f021007879dcd9e2bca795b4758e187fa1c3b302`.
The selected optimized source is the terminal-stack implementation recorded in
`terminal-query-review.md`, not the original dense callback. No Rust, protocol,
proof-body, CU, or production setting is changed by this continuation.

Inspected selected source SHA-256 pins:

| File under `experiments/` unless stated | SHA-256 |
|---|---|
| `structured_weights.rs` | `06befd20c084234ce1afa2d7cf3612a12370fdb0e98e95db30d89cf245b51089` |
| `performance_verifier.rs` | `cdccf89cba145831138e6ac93272e262e6e377f9ea9835058d0ceb38701d8c6e` |
| `relation_callback.rs` | `d7a6eff3f93e36a11525818f3fd672b1e60f71c1bf48138292cdc636ef3ba615` |
| `inactive_row_binding.rs` | `4642f1e4361aeb9f991ef917f8efdea292187fe3de9e3a9d351230859f9ad98b` |
| `performance.rs` (producer) | `f3d05496a7f1ab7f111a33792cd8329965374e246740770c6f0ff1432db87861` |
| `complete_callback.rs` | `aaf776171df5bbab9e3f18339990acb857092b59be9d84d7f5fd948254394419` |
| `complete_binding.rs` | `d35d46ac4b0128de04a333377e1d6dc801de313dce6111e3e820d3384cd9a360` |
| `crates/aspis-core/src/transcript.rs` | `be036d144b9fe0c8119d9f6fdd8ca2167d1379f7d1d785fa2f197200b9f7d119` |

## New deterministic endpoint

`experiments/OptimizedRelationRefinement.lean` constructs a relation discrepancy
game from **raw six-field compact responses**. `RawRounds` permits each response
to depend on all earlier relation challenges, but its own challenge is supplied
only to its continuation. It contains no boundary, successful-recovery,
candidate-membership, image-validity, terminal-success or discrepancy-equality
premise. Its inputs are arbitrary coefficient/functional vectors and the
actual running scalar.

The construction reuses the V7-consumed generic arity-four convolution and
compact grammar. It derives:

- The six transmitted coefficients are exactly indices `[0,1,2,3,5,6]`;
  the quartic is `claim/4-c0`, not a seventh independently supplied field.
- The literal seven-coefficient Horner evaluation equals the represented
  polynomial evaluation.
- Claimed minus honest convolution has degree at most six, boundary equal to
  the incoming scalar-minus-dot discrepancy, and evaluation equal to the
  next scalar-minus-folded-dot discrepancy.
- `RawRounds.toGame` supplies the existing causal `JointImageGame.Rounds`
  constructor with those **derived** interfaces at every round.
- `raw_acceptance_iff_terminal_zero` connects the actual modeled terminal
  scalar/dot comparison to the game's terminal-zero event for every sequence
  of challenges, with wrong sequence lengths rejected.
- `compact_tail_wrong_bound` now applies the existing `18/|K|` three-repair
  bound to this constructed raw suffix when its incoming scalar differs from
  the actual final-vector dot. This is reuse of the existing local event,
  **not** an extra additive term or a completed extraction bound.

This fills the generic compact-response/tail constructor, including the three
relation-only stages on `256 -> 64 -> 16 -> 4`. It does **not** claim the entire
optimized verifier has been translated to Lean. The field constant prerequisite
`quarter*4=1` is an arithmetic interface for the two source `half()` operations,
not a premise that any prover residual vanishes. Source parsing, the exact
QM31 representation, and structured-vector instantiation retain their own
correspondence obligations.

## Exact causal boundary in the optimized source

| Fixing prefix / operation | Next challenge / permitted adaptation |
|---|---|
| `complete_callback.rs`: independent canonical ASQ8/ASF8/account checks; `bind_attempt` binds statement digest, verifier ID and proof-account key | This supplies the statement binding to the cryptographic callback; the theorem here does not re-prove the account layer |
| `performance_verifier::semantic`: profile `AV8/payment-extraction/v1`, binding and C1 root | `lambda, chi`; C1 is already fixed |
| C2 root, registry, zero helper claim | `theta`, ten zerocheck coordinates, `mu`; C2 can depend on lambda/chi |
| Initial mask claim | Nonzero `eta` |
| Ten compact semantic responses, sequentially | Each next `z[r]` follows its response; selected payment terminal must match the carried claim |
| All three 29-column point rows absorbed together | First secure circle OOD point |
| First 29-component OOD vector, prefixed by `0` | Second OOD point, rejecting equality with the first, at most three calls |
| Second 29-component OOD vector, prefixed by `1`; first nonce | Nonzero gamma; both component vectors precede gamma |
| Inactive scalar | Nonzero kappa; the ordinary row scales remain `[kappa,kappa²,kappa³]` alongside inactive scale one |
| Deterministic compact functional description and corrected scalar; image-gate profile | Nonzero tau; ordinary scalar, chord, rows, interpolation and masks are fixed before tau |
| Compact response0 and `[0] || foldNonce` | Alpha0; only after it can final256 be chosen |
| Final256 and final nonce | Ordered q22 sample without replacement, 64-candidate cap |
| Query-batch profile | Nonzero rho; canonical root-bound opening values are already mathematically determined by commitments/queries **on the authentication-good event** |
| Verifier-derived shifted increment `inc` | Compact response1, then alpha1; response2/alpha2; response3/alpha3 |
| Deferred public structured/query/image folds and three actual coefficient folds | Final dot/scalar check; no extra challenge or witness field |

Parsing all byte fields before sampling is not a causal proof about an
adversary's chosen root-bound values. In a source/ROM game, authentication,
prequeries, retries and transcript selection must justify the fixed-word
interpretation. A prover-supplied opening is not frozen by an unproved hash
binding assumption disguised as a deterministic equality.

### The dense transcript dependency is obsolete here

The selected `structured_weights::prepare` hashes **545 public description
bytes**, not 16,384 expanded-weight bytes:

```
"AV8/functional/three-MLE-grouped64/chord/v2"   43 bytes
[20,22,10,4,4,use_x]                            6
z[10], scales[3], chord[3], interpolant[2],
  (s0.x,s0.y,s1.x,s1.y,gamma)[5]              368
64 literal compiled u16 mask values           128
                                               = 545
```

It then absorbs the corrected scalar under `CLAIM` and the 41-byte profile
`aspis-v8-image-gate-compact-functional-v2`, before tau. This description is
verifier-derived and contains all variable functional inputs; it is not an
unchecked weight hash. The dense host differential path calls the **same v2
prepare** and materializes afterward. Therefore its same-challenge algebra
comparison is meaningful. It does not establish byte-for-byte compatibility
with the original v1 dense transcript; that was a research protocol change.

### Finite transcript work inventory, not an FS advantage bound

Source inspection gives 34 absorb calls along an accepted selected callback.
There are 28 ordinary QM31 sampling calls (lambda/chi, theta/zc/mu, ten semantic
challenges, four relation challenges), five nonzero calls (eta/gamma/kappa/tau/
rho), and two secure-circle point samples in the no-retry path. The query
sampler needs three squeezed blocks in that path. One squeeze performs two
hash calls, so this gives **110 transcript hash calls** with no retries.

The literal bounded loops permit at most four blocks per ordinary QM31 call
(four limbs, eight candidate words each), three QM31 calls per nonzero call,
three QM31 calls per circle call, one first plus three second circle calls,
and eight query blocks. A conservative accepted/aborted callback cap is thus:

```
34 + 2 * (28*4 + 5*3*4 + (1+3)*3*4 + 8) = 490 hash calls.
```

This excludes statement/attempt hashing outside the callback, Merkle hashing,
any extractor replay, and the prover's own prequeries/search. It is a
source-audited control-flow count, not a kernel-checked ROM accounting theorem
or a CU upper bound. The canonical nonce block still transmits three u64s.
No PoW predicate is checked on this research path, but these nonces remain
adversarial selection powers. The performance stress mode explicitly scans up
to its declared (at most one-million) final-nonce limit for maximum-frontier
fixtures. Neither that honest cap nor zero nonce in ordinary fixtures restricts
a malicious prover; the eventual FS theorem must charge its declared resources.

## V7 reuse map

| Existing formal work | Reuse / boundary |
|---|---|
| `V5FriRelationCandidateBridge`, consumed by `Pool/V7RelationCandidateBinding` | Reused directly: honest convolution boundary and exact natural primal / `[1,a³,a²,a]/4` dual evaluation, any dimension |
| `V6RelationFold` | Reused dependency: identifies the same `1024,256,64,16` relation sizes; no extra FRI rounds are inferred |
| `V6TranscriptRelationGrammar.reconstructed_relation_quartic_has_exact_boundary` | Reused directly: exact omitted-coefficient reconstruction; its q16/profile/work/fixed-wire constants are **not** used |
| `V5RelationSumcheckSoundness` | Reused directly: coefficient representation and degree-six difference; no old candidate-family or event-count ledger is imported |
| `K1/V7Tag73JointQueryBatchSoundness` | Applicable mathematical pattern, but its concrete query vector is q16. V8 already has generic q-degree `JointImageGame.shifted`; the q16/15-numerator theorem is not imported |
| `K1/V7Tag73OperationalRelationSourceFacts` | Source-bridge pattern and natural final-line encoder identity are useful. Its raw-word q16 matching and concrete source equalities cannot instantiate V8's quotient openings by renaming variables |
| `K1/V7Tag73RelationTailSourceComposition` | Useful raw translated-intermediate design. Its Aeneas bundles target V7, not changed V8 kernels or compact functional transcript |
| `V7InactiveClaimBinding` and earlier inactive-exact conditional links | Not used as an acceptance consequence. Repaired V8 retains shifted ordinary rows; the recorded unresolved V7 assurance premise is unchanged |
| V7 direct FS compiler / retry-resource machinery | Architecture reusable, numerical/typed transcript instantiation not reused. New OOD-vector, compact-functional, image, q22 and nonce boundaries must be represented explicitly |

## Interface completion and remaining obligation

| Interface | Status after this leaf |
|---|---|
| Six-field source compact response to polynomial | Kernel-checked algebraic construction, arbitrary fields; literal parser translation remains separate |
| Every discrepancy boundary / evaluation and terminal zero | Constructed recursively from raw causal response grammar; no correspondence premises supplied for these equalities |
| Actual quotient/fold representation, distinct final points, degree255 | Existing code mathematics reusable; concrete quotient opening/source constructor is not supplied here |
| `AfterFold.same_prior` | Existing generic dot identity remains valid; final-polynomial equality to actual coefficient equality needs the concrete natural-basis map. Not newly claimed here |
| `AfterFold.zero_iff` | Existing evaluation-vector lemma remains valid; source's slots, quotient reconstruction, query order and authentication-good event still require concrete instantiation |
| Compact description to complete structured ordinary/image functional | Differential and optimisation lemmas exist; whole 1,024-dimensional source construction not derived by this leaf |
| q22 query injection to initial three-round discrepancy | Correct shifted source preserved; no unproved q16-to-q22 or raw-word-to-quotient bridge assumed |
| Optimized terminal equality | Prior `TerminalQuery` proves image fusion and exact terminal query-vector arithmetic; full structured functional/source endpoint remains separate |
| Accepted arbitrary oracle to recoverable C1/payment knowledge | Still global recovery/extraction obligation, not solved by this deterministic suffix refinement |

The next source task is to instantiate the **one actual 256-dimensional
post-query functional** from the compact ordinary description, carried image
weight and source natural-line query basis, and prove its dot identity against
the actual authenticated quotient-fold residuals. That feeds this completed
raw-response constructor and removes equality premises from `AfterFold.tail`.
It must not assume a polynomial representation of an arbitrary received word,
nor silently turn a scalar accepted suffix into pointwise query success.

## Reproduction and scope

Run `bash experiments/run_optimized_relation_refinement.sh NEW_LOG` from this
directory after obtaining the local focused-Lean resource slot. It checks
matching research/main source and olean SHA pairs for the seven named generic
dependencies, the previously recorded JointImageGame cache, pinned Mathlib,
and uses only `lake env lean -M7000` on the new leaf. No dependency or prior
bound replay was needed. The successful exact invocation was:

```
bash experiments/run_optimized_relation_refinement.sh experiments/optimized-relation-lean-v3.log
```

| Evidence | Exit | Wall | Maximum RSS | Swap | Meaning |
|---|---:|---:|---:|---:|---|
| `experiments/optimized-relation-lean-v1.log` | 1 | 14.33 s | 5,507,334,144 B | 0 | New raw datatype's universe index initially too small; not a proved endpoint |
| `experiments/optimized-relation-lean-v2.log` | 1 | 3.86 s | 5,537,234,944 B | 0 | Terminal induction needed explicit equality transport; not a proved endpoint |
| `experiments/optimized-relation-lean-v3.log` | 0 | 7.26 s | 5,691,342,848 B | 0 | All declarations checked; 12 requested axiom audits use only `propext`, `Classical.choice`, `Quot.sound` |

The fixes were a universe-polymorphic raw datatype and one small generic
terminal-transport lemma, not enlarged memory or unfolding a concrete field.
Final source SHA-256:
`98b861e3d8a4d06d2a9ffc01bb394314353dc3dbbf55efeaa4f7390d8d8e8304`.
Final olean SHA-256:
`4aaf5ff39ddecd665d0593d57f8459c629a7cb3ee7c873798af80aac4cd4941d`.
All runs used research revision `f021007879dcd9e2bca795b4758e187fa1c3b302`,
Lean 4.32.0 (`8c9756b28d64dab099da31a4c09229a9e6a2ef35`), Mathlib
`81a5d257c8e410db227a6665ed08f64fea08e997`, and matched source/olean
dependencies from the read-only main cache at
`782f2d509a7e36efa01d89194c9c813fac84fd3b`. Only this focused job held the
local compile slot. No retained `sorry`, new axiom, old unchanged theorem
replay or package build was used. The final log's unused-section-variable
warnings are not proof failures.

Proof body remains `697*16+52+24+22*621+2*296*26 = 40,282`. No new response,
nonce, claim, round, transcript call or verifier arithmetic was added. No new
SBF/host proof-generation/security probability measurement is claimed.
