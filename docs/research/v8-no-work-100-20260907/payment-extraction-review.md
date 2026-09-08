# Authenticated C1 to a checked payment witness

2026-09-08. Research branch `research/v8-no-work-100-20260907`, starting
from full checkpoint `1c1e55a7213732068a6064168628c244e40a7f32`.
The research worktree was clean at inspection. Concurrent main work was
preserved; no reset, production source change, deployment or remote job.

## Result and scope

There is now a **same-execution honest payment proof -> authenticated C1
evaluations -> recovered C1 message coefficients -> checked transfer witness**
path in the repaired research grammar.

All four honest baseline proofs passed. Each corrupted-D arm had genuine
payment semantics and recoverable C1, but all four sampled one changed fibre
and rejected at the relation terminal. **This run did not observe an accepted
out-of-radius payment proof.** It did not search for one after the fixed
cohort finished, force query values, or turn extraction from a rejected proof
into an acceptance result.

The new Lean prerequisite proves mask-invariance of the actual decoder's
raw witness-field read footprint for arbitrary mask assignments. A second
theorem derives selected-child equality from the Boolean/path residuals.
Neither assumes an honestly compiled table, an existing valid witness, or
validator success.

The access model is an **extra authenticated-opening oracle**, not a real
rewinder and not information obtainable from a Merkle root alone. Thus this
is substantive endpoint/source progress, not global recovery, 100-bit
security, adaptive ZK or matched full-transaction CU parity.

## 1. Same execution, genuine producer

[The harness](experiments/payment_extraction.rs) includes the pinned encoder,
entropy, mask and helper source modules through
[payment_source_modules.rs](experiments/payment_source_modules.rs).
It calls the actual forest transfer compiler and selected compiled semantic
terminal. The semantic producer ports the exact degree-27 interpolation and
Boolean-suffix enumeration from `v6_onefold_prover.rs:619,1348..1470` into
the repaired compact framing. It does **not** call the unmodified public V7
proof builder, because that builder has the old transcript/relation grammar.
This is a source-shaped producer port with actual semantic operations, not
an opaque prefix, invented zero responses, or a Rust-to-Lean translation.

### Trusted setup of the synthetic test, not a cryptographic trusted setup

A synthetic account fixture provisions the retained forest root by independently
folding its tree/path, and fixes pool, deployment, anchor sequence and asset
constants before proof production. It does not derive the authoritative
context inside extraction from the prover's statement. The extractor is
given this separate immutable runtime binding and the live/afterstate
transition. The outer forest-root check remains before the compiler's
temporary lane-root substitution. Spent-nullifier context is explicitly
supplied (empty for this synthetic fresh transfer).

This account fixture is not a Solana account-authentication implementation.
No real witness or owner material is printed or stored in evidence.
Equality to the synthetic original witness is only a post-extraction test
assertion; the endpoint accepts any returned witness satisfying its validator.

### Causal order executed

1. Compile a genuine 1000 -> 600+400 transfer and check its settlement image.
   Reserve deterministic **test-only** entropy once per seed through the
   existing reservation API; derive the actual C1 masks, mask-only columns,
   G, H-padding and balanced zero-factor D. No zero-helper shortcut.
2. Encode all 26 C1 columns on the actual 2^20 circle domain. Build the
   actual salted 208-bit C1 Merkle tree before lambda/chi.
3. In the explicit opening-oracle model, authenticate and recover C1 already
   at this prefix. This recovery is independent of lambda/chi, not a tuple
   obtained after adaptive C2 and moved backwards in time.
4. Sample lambda/chi, build the actual forest copy helper, apply H padding,
   and check its zero sum. Build H/G/D codewords. Baseline C2 is honest;
   the second arm adds one to D at all four slots of predetermined fibres
   0..9301, before the C2 root and all subsequent challenges.
5. C2 root precedes theta/zerocheck batching, initial mask claim and eta.
   Produce ten genuine semantic rounds, each response before its challenge.
   The independent compact replay checks the selected masked terminal.
6. Absorb all three 29-component point rows. Sample OOD0, absorb its 29
   responses, then sample a distinct OOD1 and absorb its responses. Sample
   nonzero gamma with the existing nonce field absorbed (fixed zero here).
7. Compute and absorb the actual inactive claim; derive kappa. Preserve
   ordinary scales `[1,kappa,kappa²,kappa³]`. Freeze the transported
   ordinary weights/scalar; derive fresh nonzero tau and carry the image
   covectors through the relation.
8. Response0 precedes alpha0; true final256 depends on alpha0 and precedes
   the fresh query schedule; queries precede rho. The query discrepancy
   remains prior - rho*sum(residual_i*rho^i). Each remaining compact response
   precedes its next challenge.
9. Parse the same body, replay the same semantic prefix, verify actual
   packed openings and both frontiers, then the carried relation terminal.
   Recover C1 again using **that body's C1 root** and run the witness,
   runtime, nullifier and exact transition validator.

The research framing binds a hash of canonical transfer public fields plus
a deterministic public transition representation under a distinct
`AV8/payment-extraction/v1` tag. It is not the complete deployed
statement/attempt/account preamble. No nonce search or grinding benefit is
used; actual FS retry/nonce selection powers still need a separate theorem.

### Actual observations

| Fixed seed | Honest accepted | Corrupted-D accepted | Corrupted fibres queried | Checked witness, both arms |
|---|---|---|---:|---|
| 1 | yes | no | 1 | yes |
| 2 | yes | no | 1 | yes |
| 3 | yes | no | 1 | yes |
| 4 | yes | no | 1 | yes |

Seed 1 was the initial integration preflight. The final cohort 1..4 was
declared before its run; every arm was retained, with no stop on success.
The full-domain follow-up used the **same** cohort and reproduced identical
proof IDs after adding account-provisioning and reconstruction checks.

All 80 semantic rounds and eight terminal checks passed. In each baseline,
all pointwise folded residuals were zero. In each corrupted arm exactly one
was nonzero. The first carried prior was exact. The later compact replies
did not accidentally repair the injected discrepancy, so the final check
returned `Err(Terminal)`. This is the precise checked rejection, not a
rejection inferred from a radius label.

The previous exact
`choose(252842,22)/choose(262144,22) = 0.451637932155...` remains the
**ideal fresh-query miss diagnostic**, not the observed four-seed frequency,
an FS advantage, or an extraction-failure bound. Rare folded/rho/relation
collisions remain permissible. No universal “a touched fibre always rejects”
assertion was added.

### Quotient/code checks

For each of the eight executions the producer:

- constructs the actual chord/interpolant and a quotient in the encoder's
  exact message basis by public-matrix inversion;
- checks E1=Q[1023]=0 and E2=b*Q[1022]-c*Q[1021]=0;
- checks ordinary claim equals the transported dot product;
- re-encodes both the quotient and original batched message, and checks
  `L*Encode(Q) = Encode(U)-I` at **all 1,048,576 domain positions**, with
  all chord denominators nonzero.

These are exact optimized-Rust finite checks on the executed objects, not
a new universal encoder/degree theorem. Together with the precommitted
D change they verify the intended 9,302-fibre corruption relative to that
known image-valid anchor. The no-other-9,301-anchor conclusion still uses
the earlier code overlap/quotient-space correspondence hypothesis; this
continuation does not silently claim that source-to-Lean port is finished.

One preflight found and corrected a **new fixture packing mistake**:
C1 is slot-major, but C2 is helper-major
`4*(helper*4+slot)+limb`. With nonzero H/G/D the mistaken slot-major C2
serialization made the honest relation reject. The selected parser/verifier
was not weakened or changed. The failure log is retained.

## 2. Extractor interface and exact access budget

[authenticated_c1.rs](experiments/authenticated_c1.rs) separates three stages:

```text
expected C1 root + C1Openings
  -> authenticate exact indices/canonical leaves/salts/frontier
  -> solve public source generator system
  -> StateOnlyTraceFoundation (16 semantic message columns)
  -> extract_checked(public, authoritative context, exact transition)
```

The decoder receives no witness, mask seed, pre-encoding table, expected
honest trace, private encoder state or anchor pointer. Its public inverse
matrix is constructed before production from
`CircleEncoder::encode_c1_basis_value`, on positions 0..1023. Exact M31
Gaussian elimination has 1,024 pivots and reduces the left side to identity.
The actual recovered columns equal the source's **message coefficients**,
not the LDE evaluations. Equality with the masked producer table is checked
only after the independent extraction call.

The response contains fibres 0..255, all four slots, all 26 canonical
columns, salts and a minimal C1 frontier. The selected two-tree checker is
reused with the same C1 root/data in both positions. This duplicates checking
work; it does not assert anything about C2. Only one frontier is supplied
and borrowed twice.

| Resource | Exact contract |
|---|---:|
| Explicit opening-oracle calls | 1 bundle request per extraction |
| Requested fibres / distinct evaluations per column | 256 / 1,024 |
| Root-authenticated columns / recovered semantic columns | 26 / 16 |
| Leaf+salt bytes | 256*(403+32) = 111,360 |
| Frontier | 10*26 = 260 bytes |
| Response with predetermined IDs omitted | **111,620 bytes** |
| With all 256 explicit u32 IDs serialized | **112,644 bytes** |
| Leaf hashes / internal hashes in duplicated checker | 256 / 530 |
| Public inverse storage / augmented elimination storage | 4,194,304 / 8,388,608 bytes |
| Applying inverse to 16 columns | 16,777,216 M31 multiply-add pairs |

The public precomputation's conservative dense update bound is 2*1024^3
multiply/subtract pairs, plus pivot/scaling and public matrix generation;
the implementation skips zero factors. These are operation bounds, not CU.
Rank is checked for this **specific matrix**, not inferred from code rate or
an overlap lower bound. Failure to find a pivot fails the fixed setup rather
than becoming an unchecked hint.

A q22 proof exposes only 88 evaluations per column. For an otherwise
unconstrained 1,024-coefficient column the evaluation map has nullity at
least 936. That is an opening-data rank statement, not a claim that an entire
payment transcript contains no other constraints. At least 12 q22 executions
would be needed by evaluation count alone, but **12 is not a recovery
algorithm**: random schedules need not produce the fixed contiguous set,
independence/rank need proof, and fixed-commitment replay access is absent.

### Access-model status

| Model | Status |
|---|---|
| Ideal fixed full-word oracle | Producer has fixed encoded words; explicit model only |
| Extra authenticated-opening reconstruction | Implemented and executed on same proof roots |
| Recovering openings from ROM query logs | Existing formal K1.2 APIs inspected; not connected to this executable |
| Actual replay/rewinding extractor | Not implemented; calls, retries, fuel and failure mass unbounded here |

Relevant existing APIs are `Pool/V7MerkleQueryExtractor.lean` and
`AlgorithmicCircleDecoderV7.lean`. The former extracts from a shared raw
SHA query graph and recomputes roots; it does not turn a root into an oracle.
The latter packages algorithms with completeness/soundness/runtime fields;
it is not a callable Rust decoder for the new received-word case.
The scheduler-native partial provider at implementation pin
`07b66afc22288a6ff460180242b73de4f341e02d` is noncomputable and discards
replay/K13/K14 failures. It was inspected, not replayed or treated as total
witness coverage.

The extra response is extractor/test data, **not appended to the proof**.
No claim is made that the deployed prover will answer arbitrary requests or
that the actual FS experiment allows choosing the next query set.

### Decoder capability falsification

Five malformed-opening controls per seed reject: duplicate/wrong indices,
changed leaf under the old root, wrong root, malformed frontier and a
noncanonical M31 limb.

A separate control changes one C1 evaluation and recomputes a new valid root.
Authentication succeeds and interpolation returns coefficients, but payment
validation rejects. The log's `authenticated_changed_C1_decoder_rejected`
label refers to this **whole witness endpoint**, not a rank/authentication
failure. Ordinary interpolation is not error correction. An adversary could
target the fixed sampled coordinates; no global success theorem for this
decoder follows. This is not a full accepted-proof strategy or evidence
that no valid witness exists—the original synthetic witness still exists.

## 3. New deterministic proof and exact masking audit

[PaymentMaskRead.lean](experiments/PaymentMaskRead.lean) proves:

- the source-shaped mask predicate is disjoint from every decoder read;
- arbitrary field-mask additions preserve those reads, without an
  honestly-generated-trace or decoder-success premise;
- in particular, owner-key cells and both ordered path-child digests are
  unchanged, including zero coordinates;
- `bit*(bit-1)=0`, `(1-bit)*(left-current)=0` and
  `bit*(right-current)=0` imply the selected child equals current.

The concrete footprint includes sponge rows
12,28,44,60,444,460,476,492,508,524; source path rows
`913+16*(level/4)+4*(level%4)` for all 24 levels and their successor rows;
and input occupancy row1017 columns0/1. It deliberately overapproximates
some reads by keeping all sixteen coordinates of each listed sponge row.
All 16,384 source cells were exhaustively compared with the Lean-shaped
mask predicate; there are 3,803 masks and zero read/mask intersection.

This is a kernel-checked source-shaped algebra/layout proof plus exhaustive
finite source-layout correspondence testing. It is **not** a translated
Rust decoder proof or universal selected-residuals-to-validator completeness.
Byte canonicality/shape still matter; arbitrary field assignments do not
license noncanonical raw limb encodings. The existing mask application also
balances an inactive dependent cell chosen from the same allowed inventory,
so it remains within the proved footprint exclusion.

### Why the raw zero-padding inventory is not the accepted predicate

The host `pair_forest_constraint_residuals` inventory explicitly appends
zero-padding residuals on all 3,803 mask cells. The selected masked verifier
instead computes the source `composition_parts` from:

- projected Poseidon constraints;
- schedule/path/value/occupancy/public-asset/digest semantic lanes;
- the actual copy-helper residual;
- zerocheck weighting and active H contribution;
- the existing affine C1/mask-only/G mask term, with eta.

It does not call that raw `all_zero()` inventory or append its zero-padding
class. The mask material is applied through the actual source layout API;
H padding is checked zero on active rows and balanced on inactive rows.
D is derived through the actual balanced zero-factor source routine.
No residual list was edited or cleared in this continuation.

For each of the four masked payment traces the selected compiled constraint
composition was checked at all 1,024 Boolean positions (theta=17 for this
separate diagnostic); all values were zero. The genuine semantic producer
then used its actual transcript-derived theta and passed every boundary and
terminal. These are executed checks, not a universal adaptive-ZK proof or a
proof that every arbitrary malformed trace satisfying one scalar is valid.

Masks can change off-Boolean multilinear values and later proof responses.
“Witness reads unchanged” does not mean the whole public view is unchanged
or simulated. Full-view privacy remains separate.

The older `V7DeterministicSpendWitness` theorem decodes range limbs under
older opened-column/atomic statement interfaces and imports the earlier
capstone (including conditional obligations). It is not this literal
pair-forest decoder/validator theorem. We reuse its distinction between
checked return values and coverage, not its conclusion without a port.

## 4. Event ledger and remaining implication

Let X_open be this bounded opening-oracle algorithm plus the literal witness
validator. Let X_replay be the desired extractor obtaining access through
the actual protocol/ROM experiment. Only X_open is implemented here.

All eight test arms return checked witnesses under X_open. Only the four
baseline arms also satisfy the executed acceptance predicate. The other
four contribute no accepted failure in this cohort, but provide **no**
observed accepted out-of-radius success. No sample frequency is attached
to an unknown global error term.

A total first-failure accounting for A AND NOT X_replay must retain:

1. Access/replay unavailable, aborted or out of fuel; missing responses and
   restored/cached/advance challenge mismatches.
2. Root, canonicality, authentication or source-model mismatch.
3. Insufficient/rank-deficient/wrong-basis data, or received C1 outside the
   implemented reconstruction capability.
4. Recovered coefficients whose point/semantic/copy/path or actual
   payment/runtime/nullifier/transition validation fails.

Take each class only after excluding earlier classes to make the accounting
disjoint. Successful extraction, near or far, contributes nothing.
The whole near region is not the near theorem's bad-binding event.
Provider-none and K13 scalar/pointwise, fold/list and K14-width29 cases still
require coupling to these actual outcomes.

The useful next implication is:

```
actual accepted execution
  -> pre-lambda/chi root-bound C1 access and recoverability
     OR a quantitatively bounded accepted access/recovery failure;
recoverable C1 + exact selected constraints + authenticated context
  -> the literal checked witness endpoint succeeds.
```

Neither implication is completed globally. Early C1 fixing is real in the
extra-oracle fixture; it is not yet established for the actual extractor.
No post-C2 full tuple is retroactively fixed before lambda/chi.

The exact [ledger](payment-extraction-results.json) leaves missing bounds
null. The near 105.145190-bit local ceiling is consumed by reference, not
recomputed or charged for all near failures. Four relation repairs are
already in the previous joint games; no extra 24/k or historical 396430
“semantic” charge is added. Source correspondence, authentication, FS
resources and privacy are not assigned convenient numerical probabilities.
Grinding contributes zero security bits.

## 5. Costs, evidence and decision

The wire remains

```
697*16 + 52 + 24 + 22*621 + 2*296*26 = 40,282 bytes.
```

Maximum observed body was 39,814 bytes, not a revised protocol maximum.
No extra fields, nonce, padding or rounds were added. The ordinary dense
transpose and 16,384-byte public weight absorption remain inherited costs.
The new oracle/decoder consumes extractor resources, not transaction CU.

[Evidence](payment-extraction-evidence.json) gives exact commands/hashes,
source-module pins, exit/RSS/wall/swap and axiom logs. The final optimized
eight-arm run, including matrix setup, full commitments, semantic proving,
8,388,608 full-domain chord checks and witness tests, took **91.46 s**
and **254,656,512 bytes peak RSS**, zero recorded swaps. Public matrix
setup took **1.033884375 s**. These are synthetic research harness timings,
not selected production prover latency, replay-extractor time or CU.

The new Lean leaf passed in **5.25 s**, **2,827,255,808 bytes RSS**, zero
swaps, using only propext/Classical.choice/Quot.sound. No new axioms/sorry,
package replay, old near replays, SBF build or remote infrastructure.

Existing root-product/paired/high-J, T512/image kernel, unshifted/late-inactive
and shifted-query/later-repair regressions remain unchanged. No old fixture
was relabelled as a payment proof. The V7 inactiveExact assurance item is
carried forward unchanged; this research does not repair V7.

**Decision:** the honest end-to-end extraction slice is now executable under
explicit authenticated-opening access. It is no longer two unrelated
fixtures. An accepted D-corrupted slice was not observed in the fixed
cohort, and fixed-matrix interpolation is demonstrably insufficient for
general corrupt C1. QM31 q22 remains worth pursuing, but no security/CU/ZK
completion is declared. q23 and quintic remain unapproved controls.

**Single next experiment:** replace the extra-opening provider with a
source-shaped K1.2 raw hash-query-graph extractor, snapshotting the graph
at the C1 commitment boundary before lambda/chi. Feed only its root-bound
output to the current coefficient/witness pipeline, count actual queries,
missing/default subtrees and failures, and retain the authenticated-C1
corruption control. This tests whether the needed early access exists
without inventing arbitrary prover cooperation or query rewinds. Stop on
the first graph/grammar/coverage mismatch and preserve it; do not discard
failed branches or call full-word existence an efficient decoder.
