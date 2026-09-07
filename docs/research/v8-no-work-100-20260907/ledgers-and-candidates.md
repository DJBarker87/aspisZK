# Error events, candidate transcripts and applicability gates

Let K=F_(p^4), E=F_(p^8), p=2147483647. Exact rational outputs and approximate
display bits are in candidates.json. Decisions compare integers before logarithms.

## A. Raw interactive and fixed-prefix ledger

| Event | Exact bound | Law, hypotheses, adaptation, evidence |
|---|---|---|
| Initial width-29 curve fails coherent recovery | 336869026605739/(p^4-1) | Uniform nonzero gamma after C1/C2/claims; exact initial circle encoder, support >38229, degree-28 challenge curve; V6PublishedTheoremInterfaces + V7ExactCorrelatedAgreement. 75.740819 bits; actual restored event lifting remains separate |
| Restored point-compatible gamma residual | Same numerator/(p^4-1) | Distinct event in V7Tag73RestoredCausalErrorLedger; cannot drop it because another gamma term is already counted |
| One-fold curve failure | 9396508281246/p^4 | Uniform alpha0 after relation message and fold nonce; exact final encoder/support >9557, degree-three curve. 80.904738 bits |
| All q indices lie in a fixed bad set B | choose(A,q)/choose(N,q) | Uniform distinct indices, B fixed before sampling, |B|<=A. Applicability fails if B is selected using future query coordinates without the causal reduction |
| Same event under cap C | choose(A,q)/sum_f<=cap count(N,q,f) | Enforced conditional sampling only, as in security-contract.md. Selected V7: 76.459991 uniform bits, 73.006543 conditioned bits |
| Nonzero query residual cancels | (q-1)/(p^4-1) | Residual vector fixed before rho, conditioned on authenticated leaves and prior transcript; sequential powers, no independence across residuals assumed |
| Fixed-family semantic/copy/point failures | 396430/(p^4-1) | Exact source inventory below; roughly 105.4 bits, not a resource-independent NI bound |
| Authentication | Symbolic e12 in raw oracle model; digest exposure/target terms in NI game | Two typed salted trees, common topology, fixed canonical leaf bytes; use K1.2 query-graph theorem, not a birthday slogan |
| Extraction, sampler exhaustion | Actual classifier/extractor error; exhaustion rejects | Rejection affects completeness; conditioning a proof must explicitly change the law. No invented small extraction number |

`V7K15FailureRootInventory` gives the 396430 numerator as
27000 + 100 + 1000 + 2400 + 1 + 1 + 36600 + 36500 + 292800 + 2 + 24 + 2 + 0.
In order: ten-round repair, helper cancellation, zerocheck, theta lane, mu=0,
inactive chi, active poles, copy chi, tuple compression, OOD mix, relation alpha,
kappa point-row, gamma point-lane. The factors 100 are causal candidate-family
counts; active-pole classification precedes the non-pole Wronskian bound.
The final zero uses already-established point-compatible K1.4, not an omitted check.
This contains relation/OOD terms, so do not add the same events twice when forming
a final theorem. The historical V8 arithmetic additionally overcounts some
relation terms conservatively; it is still conditional on its changed events.

The operational K1.4+K1.5 subtotal is
673738053607908/(p^4-1), approximately 74.74 bits. Adding that subtotal, the
fold term and the conditioned q16 term already misses 100 bits. This is an
upper-bound certificate failure, not a constructive attack or lower bound.

## B. Non-interactive ledger

Use the exact game and equation in security-contract.md. Q counts every first-run
adversarial SHA call, including ordinary offline attempts and all nonce regions;
R counts atomic output/advance fork requests. Restorations replay the same hidden
tape from the start, preserve prior tables, and account for all later actor calls.
K1.2–K1.5 errors must be probabilities in that actual finite master-tape experiment.
Their raw fixed-prefix numbers cannot silently stand in for adaptive event measures.
The compiler adds (F+choose(F,2)+F*G)/2^256, once. There is no extra BCS factor.

The harness varies Q=2^20,2^36,2^40,2^48,2^54 at R=259 solely as sensitivity
analysis, and separately shows ideal 208-bit birthday probabilities at exposure G.
This is not a claimed K1.2 coefficient. The previous V8 conditional ledger uses
(1511*2q+choose(F,2))/2^208, its own stated query-graph hypothesis. It yields
100.318233 bits for q21 and 104.266662 bits for q22, assuming a 28-root fixed-tuple
gamma argument, a three-root fold replacement, two-point uniqueness, and its
stated Q/R envelope. None of these totals includes a newly proved V8 source
composition or a concrete Poseidon advantage. They cannot be advertised as
unconditional 100-bit security.

For comparison only, if a proof of a changed design incurred a Q-fold lifting
on a 105-bit raw term, Q=2^36 would reduce that term to 69 bits. This does not
assert that the custom compiler has this factor; it demonstrates why its actual
operational stage measures must be instantiated before quoting a number.

## Primary: component-wise OOD tuple binding, retained QM31

Latest applicability correction: `recovery-counterexample.md` refutes the
unconditional 28-gamma initial-recovery replacement, with an explicit 99.246-bit
isolated-stage boundary. The historical 104.266662-bit total below remains only
a conditional arithmetic model. Repair requires joint event accounting or a
changed recovery theorem, not filling a source-interface structure alone.

Continuation status: user accepts the canonical q22 40,282-byte model.
`chord-verdict.md` derives honest quotient/code-space closure and records exact
basis tests, while exposing reverse-image and transformed-relation obligations.
The restored coherent-extraction provider below is still missing; its uniqueness
theorem does not prove existence. No security applicability flag is upgraded.

Research specification: keep semantic order through the 87 point claims and
terminal check. Then sample secure circle point zeta0 and absorb a 29-K vector;
sample a distinct secure zeta1 (bounded retries) and absorb its 29-K vector.
Only then absorb the selected batch nonce and sample gamma. Replace the two old
scalar OOD values by these 58 component values and the corresponding two-point
chord quotient, following the prior v8_deep prototype. Continue kappa/relation0,
fold nonce/alpha0, final256, final nonce, a single direct bounded q21 or q22
sample, rho/query batching and relation rounds 1–3. New profile and domain labels
must distinguish this from V7. The entire schedule must be source-bound before use.

Fields: C1 stays M31; all C2, semantic/PCS challenges and responses stay K.
Maximum fixed count is 697, not 641. Canonical q21 body is 39037 bytes; q22 is
40282. The prior packed q22 body is 39934: saving 348 bytes reintroduces packed
fixed parsing, which the selected V7 deliberately traded away for CU.

The conjectured fixed-tuple event uses a <=100 tuple family fixed before both
OOD points. A conservative two-point collision bound is
100^2*1024^2/((p^4-p^2)*(p^4-p^2-1)). Then a fixed unequal tuple polynomial in
gamma has at most 28 roots. This is not valid for arbitrary challenge-dependent
tuples. `ExactCompilerPreGammaTupleObligation` on the prior branch explicitly
requires a restored K1.4 provider; there is no constructor covering all cached
and advance continuations. Also missing: exact affine-chord quotient-to-released
circle-code/fold bridge. Generic polynomial identities do not authenticate it.

Reuse: field/parser/Merkle kernels, payment semantics, existing fixed-tuple and
chord algebra lemmas, source bounds. Modify: profile, transcript, OOD/deep query
kernel, sampler and source bridges. New mathematics: actual pre-gamma tuple
selection, quotient degree/encoder link, complete adaptive privacy and NI event
composition. Prior q22 rank witnesses had legal/physical/helper containment but
do not prove all schedules. No mask removal is budgeted here.

## Fallback: selectively lift PCS to E, initially retain semantic K

Keep 16 semantic plus ten mask-only M31 C1 columns, and H/G in K. Widen D to E.
Keep semantic randomness and 28-column point claims in K; widen the D point
claims, inactive combination, gamma/kappa/OOD mixing, relation messages/alphas,
rho and final256 to E. Commit C2 only after lambda/chi as before. All messages
whose values depend on a wide challenge must have wide response slots.
Every PCS E sampler, secure circle exception set, and retry rule needs its own
profile and proof. Reusing a 16-byte QM31 sampler is not field lifting.

The modeled fixed split is 355 K values (1+270+3*28) and 286 E values
(3 D claims+1 inactive+2 OOD+24 relation+256 final). The record is
403 packed C1 +124 packed H/G +124 packed D +32 salt =683 bytes.
At full domain 2^24, q16 and cap272, body is 39980 including 24 nonce bytes.
Uniform bad-set query bound is 111.062958 bits; after cap conditioning it is
109.390276. These use the m=12 agreement cap floor((25/24)*sqrt(256*Npost))
=34133 as a hypothesis requiring a new exact decoder/curve theorem.

Field-size substitution screens give ~199.74/~204.90 gamma/fold bits with
unchanged numerators; they are not theorem ports. Semantic/copy terms remain K
and can dominate. In particular the old fixed-family factor 100 cannot simply
be reused at new multiplicity/domain/list bounds without rederivation.

Descent lemma (proved algebraically here, not in Lean): if A is an m-by-k matrix
over K with rank k and c in E^k satisfies Ac=b in K^m, choose k independent
rows A0. Its inverse is over K, so c=A0^-1 b0 is in K^k. For a degree-<k
evaluation code, k distinct points give a nonzero Vandermonde determinant;
nonzero GRS row multipliers preserve rank. The initial Aspis encoder instead
uses its exact k-dimensional released image, so the required rank statement
is about its actual generator matrix, not a dimension-(k+1) ambient surrogate.
Apply descent only after authenticated base-valued leaves give enough matching
coordinates of the extracted codeword. Malicious leaves outside the subfield
must be rejected canonically; sparse query agreement alone does not give full
outputs/rank. This missing extraction step is not replaced by the lemma.

Hiding falsifier: for w,r in K, the E disclosure v*w+r exposes w in its v
coordinate despite a uniform K mask r. The Rust prototype checks this example.
It does not prove that a proposed Aspis disclosure has exactly this leak; it
refutes the inference that a narrow mask automatically hides a widened response.
An E-linear full-view mask image must contain every legal same-statement witness
difference at each adaptive prefix, including disclosed final256 and selected
queries. Wide D may help, but its mixed gamma powers, subfield leaves and semantic
constraints make surjectivity nonautomatic. Any extra masks/openings consume the
20-byte margin. No complete simulator is supplied in this run.

## Full quintic control

Replace all K challenges/helper messages by F_(p^5), retaining M31 semantic
inputs and the one-fold layout; regenerate all field-dependent transcripts,
encoder/theorem bridges and masking. There is no embedding of F_(p^4) in
F_(p^5), since 4 does not divide 5. The independently certified polynomial is
X^5-X-6. q21 canonical body is 41692; q23 is 44276. Even q21 exceeds 40 KiB;
packed fixed q21 is 41292 (still +332 over 40 KiB). Query-only q20 cannot
reach 100 bits at A=9557. This is a useful arithmetic control, not the preferred
CU route; the reference quintic inversion is deliberately unoptimized.
