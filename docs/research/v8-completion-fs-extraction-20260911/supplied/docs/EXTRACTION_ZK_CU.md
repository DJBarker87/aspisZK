# Extraction, complete payment semantics, ZK and compute resources

## Decoder/extractor starting point

Two independently implemented prime-field decoders are delivered:

- `polynomial.berlekamp_welch`: exact RREF solution of Q(x_i)=y_i E(x_i),
  monic degree-t locator, exact polynomial division, degree and error checks.
- `gao.gao_decode`: vanishing polynomial, checked interpolation and extended
  Euclidean reduction, followed by exact division and agreement checking.

The first is a useful small-instance oracle; the second avoids the cubic
Gaussian solve and is a better algorithmic starting point for larger samples.
Neither implements the selected QM31 tower/circle basis. Do not relabel the
prime-field tests as validation of that implementation. Bind canonical field
limbs, field homomorphisms, natural-circle-to-GRS conversion, image constraints
and the actual degree before substituting a deployed decoder.

For a scalar RS message dimension k, t arbitrary symbol errors and distinct
sample points, n>=k+2t is the reference condition. In Aspis, count the actual
symbol errors induced by bad fibres and the transformed polynomial degree;
do not substitute a fibre count for a symbol count or assume dimension1024
means degree<1024 after every circle transformation.

`GaoInvariant` proves a first-attempt Bezout preservation identity and the
candidate agreement implication outside locator roots. `DecoderUniqueness`
proves the Hamming-support triangle and generic unique-close-codeword result.
Its actual code-separation producer is still needed. `CommonSupport` transports
one shared bad set across all columns and accounts for explicit pole losses.

A complete proof should track: interpolant equals sampled data; vanishing
polynomial roots/distinctness; Euclidean invariant; degree stopping bounds;
nonzero locator; exact divisibility; selected message/image membership;
canonical coefficient descent; and a runtime bound on the actual arithmetic
implementation. Verify the output rather than trusting solver status.

## Permitted information, not a hidden opening oracle

The root does not supply all its leaf preimages. FrozenAccess offers only the
recorded authorised prefix and raises MissingAnswer for everything else. Build
candidate material from the actual query graph or a formally authorised rewind
construction. Missing information is a genuine extractor failure/obligation.

A family with at most one mathematical member is not automatically computable.
Prove how it is found without enumerating the entire field, all messages or all
hash inputs. Classical choice can support an existence theorem but not a claimed
polynomial-time algorithm.

For private sampling, fix the word before the sampler's coins. Prove the
sample law, common support and failure tail. For forking, group branches by the
same causally fixed prefix and count the work of every attempted branch. Keep
censored and aborted branches. The delivered collector cannot make an
insufficient/incoherent set of forks succeed by filtering the denominator.

## Complete selected payment relation

Use the same tuple throughout owner secret, note opening, input membership,
nullifier, asset, amounts, output commitments, append state and runtime effects.
The selected layout is a two-output forest with 24-level input membership;
older depth-20 one-output V7 endpoints cannot be transplanted by matching names.

TransferAmounts is deliberately limited. The inverse-product identity supplies
nonzero field values; positive bounded integers require canonical/range facts.
Integer conservation must be derived without modular wraparound. The reference
amount check rejects zero recipient/change and values outside the 30-bit range.

PaymentTransition records a tiny nullifier/append state slice to demonstrate
executable success implying effects and replay rejection. It contains no claim
of authenticated forest roots, authority, actual Poseidon/copy semantics or
Token custody. Those require the existing selected source interfaces and
independent validator, not an extra record field asserting their truth.

The final extractor should return a witness only after the actual independent
payment validator succeeds. Its theorem must prove validator soundness and
candidate availability, not only the trivial conditional fact that a search
returns a candidate it has been told is valid. Preserve input-history binding,
program/deployment identity, registry state, account ownership, asset matching,
nullifier freshness and atomic settlement.

## Adaptive full-view zero knowledge

Define the observer's complete view and the intended adaptive interaction count.
Static masks can hide one projection while the joint view leaks information.
Rank tests are a falsification aid, not a simulator proof.

The delivered static linear criterion is: for mask map L and witness-dependent
view shifts v,w, find delta with L(delta)=v-w. Translating a uniform mask by
delta is a bijection, and the two linear views agree. This is a precise useful
lemma. It does not handle nonlinear inverse/positivity data, hash commitments,
query-dependent openings or programmed random-oracle answers.

Construct a witness-free simulator for the exact repaired profile. Inventory
all material it emits and every hash answer it programs. Derive the distribution
of the joint transcript, including salts/roots, semantic/ordinary/OOD messages,
query records, retry/abort behaviour, and the adversary's own oracle calls.
A programmed point already queried by the adversary must be counted or handled,
not assumed unseen. State any additional primitive assumptions explicitly.

Keep simulator and knowledge-extractor access separate. Their algorithms may
have different allowed capabilities and randomness. A soundness proof does
not automatically justify oracle programming for privacy.

## All-reachable compute and storage

A cost proof has three layers: actual source execution produces a bounded
operation trace; calibrated/pinned runtime gives a cost bound per operation;
integer arithmetic composes them. CostTrace and cost.py only provide layer3.

Freeze the actual SBF/ELF, build flags, feature set and transaction/account shape.
Derive bounds for all variable successful paths, notably PDA searches, field
sampler retries, query duplicate handling and frontier shapes. Include transfer,
withdrawal, current/rollover history pages, account/CPI/token checks and nullifier
creation. Keep failure exits distinct from successful-path bounds.

Do not use the measured repaired transfer at1,105,880CU as the fixed part of an
all-path proof without decomposing its operations. Do not carry benchmark
claims across a profile change or silently disable overflow checks. Preserve
source maxima, unit-cost calibration hashes and the theorem connecting the
trace to the actual run. Unknown quantities remain BLOCKED in the calculator.

Resource-bounded extraction also needs time/memory/hash budgets off-chain;
on-chain verifier CU alone does not establish the extractor's feasibility.
