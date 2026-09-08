# Raw authenticated C1, totalized recovery and the circle polynomial bridge

2026-09-08. Base `7b9d3f457ea929b7d1efa9e6dbafa540f0fd4143`, branch
`research/v8-no-work-100-20260907`. Initial research worktree clean; subsequent
concurrent main work preserved. No production activation or verifier changes.

## Decision

The previous extractor's global canonicality requirement is now demonstrably
too strong: a genuine repaired research payment proof accepts while two
unopened C1 fibres contain noncanonical limbs. A byte-preserving graph
extractor, followed by totalized error correction, recovers a checked witness
from **that same execution**. This closes a concrete conservative extractor
failure, not the global accepted-extraction event.

The circle-to-RS construction is no longer supported only by arithmetic tests.
Lean constructs one degree-at-most-1024 polynomial for each natural-tensor
message, valid at every circle point; it also proves that the decoder's finite
image check implies global image membership under the explicit degree/index
conditions. An all-domain Rust check verifies the actual ten single-bit
coordinate factors and distinct points. The remaining full FFT/source
translation and Gao algorithm completeness are not claimed complete.

The profile remains QM31 q22 and **40,282 bytes maximum**. This continuation
changes extractor handling and research fixtures only: zero new proof bytes,
transcript challenges or verifier operations. It establishes no new global
security level or CU measurement.

## 1. Same-execution noncanonical control

With fixed seed 1, the producer overwrites the packed semantic-column-0 limb
in all four slots of fibres 0 and 256 with `p=2^31-1`, the sole noncanonical
31-bit encoding. This is done in raw leaf assembly **before** the C1 root,
lambda/chi and all later challenges. The honest coefficient table, valid
transfer, masks, H/G/D construction, semantic producer, image gate, shifted
ordinary rows and shifted query batch are retained. Every later root, claim,
challenge and response follows the normal repaired research order. No seed
or support is selected after observing queries.

| Stage | Observed result |
|---|---|
| Old strict whole-tree extractor | `Canonical` failure |
| New raw graph traversal and independent root rebuild | Success; exact original bytes retained |
| Both strict coefficient windows | `Canonical` failure |
| Totalized Gao recovery, 1,153 points | Eight erroneous samples corrected; two totalized bad fibres |
| Recovered coefficients / checked witness | Original synthetic coefficients recovered; literal validator accepts |
| Actual q22 schedule | Neither malformed fibre queried |
| Actual semantic/repaired relation replay | Accepts |

Proof ID:
`79cb3ccd6a4731f8c7c1a5f5659575eb7f22503466d73740b446f36303f741f7`.
C1 root: `e85b1e1c8f85a703f19b718212bc65e35decb437e96210c17e67`.
Body: **39,346 bytes**, below the unchanged 40,282-byte maximum.

This refutes “acceptance implies all committed C1 limbs are canonical,” not
payment knowledge. A valid witness exists and is extracted. One fixed
accepted execution is not an attack-rate measurement. No favourable seed
search was performed. If a malformed fibre is queried, the fixture records
the opening-parser rejection instead of unwrapping it or continuing with a
fabricated value. The observed execution did not take that branch.

The five new small raw-entry controls include a direct call to the selected
`gamma_combine_v6_packed_layer0`: it still rejects the malformed C1 encoding.
Its canonicality rules and verifier acceptance were not changed. The 5,040
orders of the existing seven-node graph were rerun because the traversal
signature changed; all 80 causal orders succeeded and the other 4,960 failed.
That is enumeration of one fixed graph's orders, not all adaptive strategies.

## 2. Authentication and arithmetic are different interfaces

`extract_raw` checks typed preimage lengths, tags, hash-query order, root
identity, collision consistency, depth and fuel. It preserves every raw leaf
byte. It does **not** decode or normalize field values while hashing.
`extract` retains the earlier strict mode as an explicit regression control.

For coefficient recovery alone, `totalized_value(fibre,slot,column)` applies
strict limb decoding and maps a decoding failure to M31 zero. It checks the
array indices first. This is the literal convention of
`Pool/V7ExtractedLaneWords.lean:c1Received`, which maps
`decodeC1EntryExact(...).map embedM31Exact` through `getD 0`. It is not an
instruction to accept noncanonical opened evidence, reduce arbitrary bytes
modulo p, or rehash altered bytes under the old root.

Gao's sample construction and its full-word distance check now use this same
totalized word. The full-word cap is a cap on **totalized semantic C1**; it is
not necessarily the number of malformed raw limbs. An invalid encoding that
totalizes to the true zero symbol need not count as a code disagreement.
The raw bytes remain independently authenticated in either case.

The extractor reads the instrumented private SHA-query prefix frozen at C1,
not a public proof account or Merkle root alone. It receives no witness,
producer coefficient table, salts/tree pointer or expected anchor. Synthetic
witness equality is checked afterwards only. The graph log is not persisted.
Actual adversary/replay coupling, Q/time/memory limits and authentication
failure probabilities remain separate FS obligations; the honest log size
does not bound malicious resource use.

## 3. New kernel-checked mathematics

All results are in [CircleLaurentRecovery.lean](experiments/CircleLaurentRecovery.lean).
Let K be a field with constants i,h,g satisfying

    i^2 = -1, 2*h = 1, 2*i*g = 1.

For x^2+y^2=1 and z=x+i*y, define

    C_m(X) = h*(X^(2m)+1), S(X) = g*(X^2-1).

`circle_scaled_xy` derives `C_1(z)=z*x` and `S(z)=z*y` from those equations.
`cosine_double` proves the scaled recurrence; induction then gives
`C_(2^j)(z)=z^(2^j)*T_(2^j)(x)`. No circle-polynomial representation or
post-challenge choice is assumed to establish these identities.

Each active tensor bit uses its corresponding scaled polynomial. An inactive
bit uses **X^m**, not 1. Thus every row carries the same total shift:

    weights = [1,1,2,4,8,16,32,64,128,256], sum = 512.

Products have degree at most 1,024, including rows with zero message
coefficients. Summing these products proves `natural_tensor_embedding`:
for every message there exists one polynomial P, of degree at most 1,024,
whose evaluation at **every** circle point equals z^512 times the natural
tensor evaluation. The polynomial is constructed from the message, not
chosen separately for each point. `circle_z_nonzero` justifies unscaling.

`checked_image_global` handles the actual image-check issue: an arbitrary
candidate polynomial of degree at most 1,024 that agrees with that scaled
message on more than 1,024 distinct circle points must agree everywhere.
It does not assume that the candidate was already in the circle image.
The implementation's 1,153- and 2,052-point checks exceed that threshold.

`totalized_agrees` and `totalized_bad_fibres_le` prove that totalization
preserves every correctly decoded symbol and cannot create extra bad fibres
outside the common raw-disagreement set, across every column and slot.

| Interface | Status |
|---|---|
| Circle identities, doubling and tensor degree | Kernel checked, symbolic over a field |
| Message polynomial fixed for all circle points | Kernel checked |
| Finite image check implies global image | Kernel checked with candidate degree and distinct points explicit |
| Totalization preserves common support | Kernel checked |
| Actual source single-bit factors / domain points | Exhaustive optimized Rust finite check |
| Source message FFT equals the natural tensor sum | Inspected; universal Rust/Lean refinement still open |
| Gao Euclidean-loop completeness and resource theorem | Still open as a kernel/source port |
| Acceptance forces recoverable C1 and payment residuals | Still open globally |

The final leaf/axiom audit used only cached Mathlib imports, no concurrent
Aspis olean. It exits zero with `propext`, `Classical.choice`, `Quot.sound`
only; no new axioms or `sorry`. Small preflight errors in local degree and
decidability expressions were fixed before retaining the result. No unchanged
near-gamma, package-wide or generated-certificate replay was run.

## 4. Actual source/index gate

[source_coordinate_gate.rs](experiments/source_coordinate_gate.rs) exhaustively
checks all 1,048,576 realized log-20 circle points, their distinctness, circle
equation and CM31 scaling identities. At every point it compares all ten
`encode_c1_basis_value(1<<bit,index)` values to
`y,x,T2(x),...,T256(x)`: **10,485,760 exact source comparisons**.

This avoids constructing 1,024 full encoded unit vectors. It establishes the
finite point/twiddle bridge in the executed optimized source, but is not a
kernel certificate or proof of the mutable `encode_c1_message` FFT loop.
The sparse accessor follows the source's selected-bit product. Older
`V5FriInitialCircleEncoderIdentity` is useful related mathematics, but its
displayed initial theorem uses a 2^19 domain and an explicit `encoder1`
premise. It was not silently substituted for this V8 log-20 source bridge.

## 5. Resources, ledger and remaining event

| Focused job | Wall time | Peak RSS | Swap |
|---|---:|---:|---:|
| Noncanonical genuine-payment harness | 47.21 s | 592,330,752 B | 0 |
| Gao portion of that harness | 0.777 s | Included above | — |
| All-domain coordinate gate | 0.54 s | 28,966,912 B | 0 |
| Raw graph controls/order enumeration | 1.15 s | 2,015,232 B | 0 |
| Final Lean leaf and axiom audit | 12.42 s | 2,852,962,304 B | 0 |

The payment harness deliberately runs the old strict extractor before the raw
one to exhibit its failure, so its total is not an optimized extractor time.
It also includes producer commitments, semantic rounds, source re-encodings,
full-domain quotient checks and repeated fixture validation. It is neither
production proving latency nor complete-transaction CU. No SBF, pool program,
remote build or deployment ran. Raw input payload remains 238,287,374 bytes
for this synthetic C1 prefix; it stays in local memory, not disk/network logs.

For X_raw_checked, the total residual is still `A AND NOT X_raw_checked`:

1. Raw graph/access/resource/source failure on an accepted execution.
2. Raw graph returned, but all bounded candidate/decoder paths fail to return
   a witness passing the actual payment/context/transition predicate.

Noncanonical data alone no longer forces class 1 in the raw mode. It can
still contribute ordinary decoder disagreement in class 2; malformed typed
preimages and all replay/provider-none branches remain visible. Successful
noncanonical extraction contributes zero to failure.

The previous [exact sampling ledger](c1-sampling-results.json) is reused,
not recalculated as a new security claim. Its hypergeometric bound is
conditional on the fixed **totalized** C1 word being within 16,535 common
fibres of a code tuple, distinct source evaluation points, correct unique
decoding and independent ideal private sampling. Totalization preserves a
raw common-support guarantee; it supplies no missing radius/semantic premise.
The new deterministic lemmas add no probabilistic check or security credit.
The fixed SHA test coins still do not establish the ideal sampling law.

[Machine-readable results](raw-c1-results.json) leave accepted general
decoder failure, source/FS, semantic/payment coverage, full-view ZK and
complete-transaction CU unbounded/unmeasured. Existing near/image/row terms
are not re-added or double-counted. All previous counterexamples remain
regressions. No field, query or size relaxation is taken.

**Next decisive step:** prove the bounded Gao recovery interface (success
within the justified punctured-code radius) and connect its returned source
message to the early C1 semantic constraints. The all-domain factor check
and symbolic polynomial theorem now give a precise encoder boundary for that
work. Keep far/no-cover accepted mass and tuple-to-payment failures explicit;
closing this local decoder step will not by itself settle them.

Commands, pins and phase-specific evidence: [raw-c1-evidence.json](raw-c1-evidence.json).
