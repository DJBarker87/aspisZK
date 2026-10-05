# Question B: 100-bit knowledge soundness of the R102 profile with no grinding

Base `4e0f47381`, profile `AV8/R102/sparseG-bitperm-two-swaps/quadratic-channel-fold/merkle8-research-v1`.
Written for a reader who has not seen the repository. Node ids (S12, …) refer
to `lean/V8Audit/Soundness.lean` in this directory.

**Verdict: OPEN. The stop condition triggered.** Two of the nine round
targets, gamma and alpha0, rest on a bound that does not exist at these
parameters: they are root counts for a tuple family fixed before the
challenge, and no theorem supplies that family for every accepting branch. The
only theorems in the tree that bound those two rounds at the R102 thresholds
give 75.74 and 80.90 bits. No accepted forgery and no sub-100-bit attack is
exhibited. Per the audit rules this note stops at the ledger and does not
attempt a new argument.

## 1. Protocol and exact parameters

- Fields: $\mathbb F_p$, $p=2^{31}-1$; challenge field $K=\mathbb F_{p^4}$,
  $|K|=p^4\approx 2^{124}$.
- Committed data: 26 columns over $\mathbb F_p$ (C1), 3 columns over $K$ (C2:
  $H_1$, $G$, $D$). C2 is committed after two challenges that depend on C1.
- Initial code: evaluations on a circle domain of $N=2^{20}$ points of the
  1024-dimensional coefficient space; rate $\rho=2^{-10}$. The basis transport
  $T$ of R16/R84 is a bijection of the coefficient space (Lean:
  `AspisV8R16.inverse_transport`, `transport_inverse`; node S31), so the
  codebook is the V7 codebook.
- Fold: one four-to-one fold to a domain of $2^{18}$ fibres; final message
  *Final256*, degree at most 255, dimension 256, rate $2^{-10}$.
- Agreement thresholds: more than 38229 of $2^{20}$ symbols (initial), more
  than 9557 of $2^{18}$ fibres (final). Both are $(7/6)\sqrt\rho=0.03646$ as a
  fraction; the Johnson bound is $\sqrt\rho=0.03125$. Relative proximity
  parameter $\delta=0.96354$. Everything is inside the Johnson radius; no
  conjectured proximity gap is used.
- List sizes: at most 100 (initial) and 99 (final) codewords
  (`baseline.md`; V7 chain `AspisFormal/AspisFormal/K1/V7ExactCorrelatedAgreement*.lean`;
  the published-interface expression caps in
  `V6PublishedTheoremInterfaces.lean` are 112 and 113).
- Out-of-domain: two sequential distinct circle points; the prover answers
  each with all 29 component values (58 values).
- Queries: $q=22$ distinct fibres; each record opens four points of all 29
  columns.
- Commitments: SHA-256 truncated to 26 bytes (208 bits); two trees of arity 8
  and depth 6 over $8^6=2^{18}$ leaves; one 32-byte salt per leaf index shared
  by both trees.
- Fiat–Shamir: SHA-256 duplex with 256-bit state; bounded-rejection samplers.
- Grinding: three prover-chosen nonces are absorbed; no leading-zero check
  earns credit. Every oracle call counts toward $Q$.

Interactive order: C1; $\lambda,\chi$; C2; ten degree-27 semantic rounds; 87
point claims; OOD point 0 and its vector; OOD point 1 and its vector;
$\gamma$; inactive claim; $\kappa$; channel coefficients $p_0,p_2$; $\beta$;
$\tau$; relation round 0; $\alpha_0$; Final256; 22 queries; $\rho$; relation
rounds 1–3.

## 2. Round-by-round ledger

Bits are $-\log_2$ of the exact rational, computed with integer arithmetic.

| # | Round | Target | Bits | Rests on | Status of that bound |
|---:|---|---|---:|---|---|
| 1 | Semantic rounds and terminal | $396430/(p^4-1)$ | 105.40 | V7 fixed-family root inventory (ten degree-27 rounds, helper, zerocheck, copy, tuple compression); includes candidate-family factors of 100 | V7 inventory; not re-derived for R102's changed OOD and channel terms. Node S10: open |
| 2 | OOD pair | $100^2\cdot1024^2/((p^4-p^2)(p^4-p^2-1))$ | 214.71 | Two distinct tuples of a list of 100 agree at both points | Paper, given a pre-committed list (S20). Node S11: open |
| 3 | $\gamma$ | $2800/(p^4-1)$ | 112.55 | Degree-28 root count, times 100 tuples | **No bound exists** without S20. Node S12: open |
| 4 | $\beta$ | $2/p^4$ | 123.00 | Degree-2 identity in $\beta$ | Identity proved (`ChannelFold.quadratic_dot_product`, S32); needs the pair fixed before $\beta$ (S21). Node S13: conditional |
| 5 | $\tau$ | $4/(p^4-1)$ | 122.00 | Root count of the image residual polynomial | Proved for a fixed residual vector (`badImageChallenges_card`, S33, at most 3 for four residuals; the combined gate is degree 4). Node S14: conditional on S21 |
| 6 | $\alpha_0$ | $300/p^4$ | 115.77 | Degree-3 root count, times 100 | **No bound exists** without S20–S22. Node S15: open |
| 7 | Queries | $\binom{9557}{22}/\binom{262144}{22}$ | 105.14 | Uniform distinct schedule misses a fixed bad set of size at most 9557 | Schedule law proved on independent answers (`R417.uniform_success`); bad set fixed before sampling needs S20–S22. Node S16: conditional |
| 8 | $\rho$ | $44/(p^4-1)$ | 118.54 | Root count for 44 residuals | Proved for fixed residuals (`badCombinedChallenges_card`, S34). Node S17: conditional |
| 9 | Relation rounds | $24/p^4$ | 119.42 | Four degree-6 rounds | Paper, given S21. Node S18: open |
| | **Sum** | | **104.26** | | Conditional on rows 1, 3, 6 |

The sum is $2^{-104.2615}$. It reproduces, up to the commitment term, the
"104.266662 bits for q22" of the 7 September conditional arithmetic
(`ledgers-and-candidates.md`), which that document says "cannot be advertised
as unconditional 100-bit security".

Commitment and compilation terms, not rounds:

- Binding: two openings of one root agree or exhibit a hash-trace collision
  (Lean: `R552.depth6_leaf_path_binding`, node S30). In the random-oracle
  model a collision among $Q$ outputs of 208 bits has probability at most
  $Q^2/2^{209}$: constant at $Q\approx2^{104}$.
- Compilation (node S03, open). The target shape is
  $\Pr[\text{accept without witness}]\le(Q+1)\sum_i\epsilon_i+3(Q^2+1)/2^{208}$,
  the form of the BCS transformation for round-by-round knowledge soundness
  (Ben-Sasson, Chiesa, Spooner, *Interactive Oracle Proofs*, TCC 2016-B;
  round-by-round form in Chiesa and Yogev, *Building Cryptographic Proofs from
  Hash Functions*, 2024). Parameter check: **not done**. Those theorems assume a
  public-coin IOP with uniform challenges; R102 has prover-chosen nonces,
  bounded-rejection samplers, a first-valid query sample and a C2 commitment
  that depends on earlier challenges. Theorem numbering was not re-verified
  against the published texts in this audit.

**What "100 bits" means here.** Reading (i): the round errors sum to at most
$2^{-100}$, so a prover needs about $2^{100}$ oracle queries; the conditional
sum meets this with 4.26 bits to spare and the 208-bit digest gives about 104.
Reading (ii), the repository's own contract (`security-contract.md`, gate 2):
acceptance without extraction at most $2^{-100}$ for every adversary inside a
published envelope $(Q,R)$. With a compiler linear in $Q$ and $Q=2^{36}$ the
query row alone gives $2^{-69.1}$. Reading (ii) is reachable only through a
compiler that charges adaptive stage events without a factor $Q$, as V7's
`V7Tag73ExactFixedK16Closure` does for V7; no such theorem exists for R102.

## 3. Do the V7 theorems apply at these parameters?

1. **List decoding.** Yes for the code: same domain, dimension, thresholds;
   the transport does not change the codebook (S31). Not rebound in the audit
   skeleton (node S24: open).
2. **Correlated agreement.** The V7 chain (files
   `AspisFormal/AspisFormal/K1/V7ExactCorrelatedAgreement*.lean`; caps
   `initialBatchChallengeCap` and `foldChallengeCap` in
   `V6PublishedTheoremInterfaces.lean`) bounds, for the exact encoders at
   thresholds 38229 and 9557, the number of challenges for which a width-29
   degree-28 batch, or a degree-3 fold, is close to the code while the lanes
   are not jointly close:

   - initial batch: $336869026605739/(p^4-1)$, **75.74 bits**;
   - fold: $9396508281246/p^4$, **80.90 bits**.

   Both are below 100. V7 reached its endpoint with proof-of-work on top of
   them. They also do not apply directly: R102's verifier tests the fold of
   the chord quotient of the batch, not the batch, and the bridge from one to
   the other is not in the tree. The published general bound in the
   list-decoding regime (Ben-Sasson, Carmon, Ishai, Kopparty, Saraf,
   *Proximity Gaps for Reed–Solomon Codes*, FOCS 2020; correlated agreement
   over lines and low-degree curves) has error
   $(k+1)^2/\big((2\min(\eta,\sqrt\rho/20))^7\,|K|\big)$ per unit of curve
   degree. Parameter check: $k=1024$, $\sqrt\rho/20=2^{-9.32}$, $\eta=0.0052$,
   so the bound is about $2^{-45.8}$ for a line and $2^{-41}$ for the degree-28
   curve: weaker than the V7 exact theorem and far from 100. The formula and
   theorem numbers are quoted from memory and were not re-fetched (gap B10).
   `decision.md` §3 records the same conclusion for DEEP-FRI (ITCS 2020,
   Theorems 3/25, Lemma 28): at most 16.6 bits from that formula here.
3. **Fiat–Shamir.** `V7Tag73ExactFixedK16Closure`
   (`exact_fixed_clean_probability_le_extraction_plus_four_terms`) is a custom
   compiler for the V7 transcript: its constants (1511 verifier oracle calls,
   16 queries, three work checks) and its four stage events are V7's. It does
   not apply to R102.
4. **Query phase.** V7 proves the conditioned q16 bound
   (`V7Tag73CausalAlphaFinalWorkQ16Probability`). For q22 the tree has the
   uniform-schedule law (`R417.uniform_success`, node P48) but not the event
   composition.

## 4. What each redesign step changed

| Step | Change | Effect on the ledger |
|---|---|---|
| V8 baseline (two-OOD, q22) | 58 component OOD values replace two scalars; 22 queries; no work credit | Introduces rows 2, 3, 6 in fixed-family form in place of the two V7 curve terms |
| R16 basis transport | Encoding $E(Tm)$ | None on the code (S31). Verifier weights transported by the dual (`inverseTransport_dot`); exact-source refinement open |
| R18 sparse-coded $G$ | Semantic mask coins are 271 code coordinates of the committed $G$ (`selected_card`) | $G$ becomes a second channel with its own weights; no new numeric term |
| R19 channel fold | $p_0,p_2$ sent, then $\beta$; one Final256 for the $\beta$-combination instead of two final arrays | Adds row 4 and obligation S21: the pair must be extractable before $\beta$; queries test only the combination |
| R84/R102 two-swap | Different permutation in $T$ | None on the code |
| R102 merkle8 | Arity 8, depth 6, parent domain `0x18` | Binding re-proved (S30); proof 57,682 bytes; collision term unchanged |
| R120 augmented query | Proof technique for privacy; verifier unchanged | None |

## 5. The open classes of the 7 September decision

`decision.md` was a no-go on certifying 100 bits, with these classes left
unbounded. For R102:

1. **Good-anchor, same-final unextracted mass.** A close anchor exists, the
   accepted execution has a valid image, a correct ordinary claim and the same
   final, yet is not extracted. **Still open** (S20, S22). R19 widens it:
   "same final" now refers to the $\beta$-combination of two channels, so the
   class also contains pairs that differ channel-wise and agree after
   combination (S21).
2. **No-close-anchor mass.** No tuple of codewords is close to the committed
   words, yet the execution is accepted. **Still open** (S20). Unchanged by
   the redesign: same code, same thresholds.
3. **Far-final accepted extraction.** Final256 is not the fold of any listed
   candidate. **Still open** (S22). The robust-recovery result of 7 September
   (105.1453 bits for at most 9,301 corrupt fibres) is a causal-game lemma for
   the earlier single-channel suffix; it is not in the tree as Lean and was
   not ported to two channels.
4. **Full-fibre counterexample.** Committed words of the actual widths (26
   base, 3 extension), zero on 9557 common fibres and a product polynomial
   elsewhere, pass both agreement thresholds for every fold challenge at
   7,072,436 values of $\gamma$, while no same-support tuple exists. This
   gives probability at least $7072436/(p^4-1)=2^{-101.2462}$ for the joint
   "thresholds pass and same-support recovery fails" event. **Unchanged**: it
   uses only the code, the widths and the thresholds, all retained. It exceeds
   the $2800/(p^4-1)$ budget of row 3 by a factor 2525.9, so row 3 is refuted
   as an unconditional recovery bound and stands only as a fixed-family bound.
   It is a lower bound on one event, above 100 bits, and satisfies none of
   the semantic, relation or authentication checks; it is not a forgery.

One further item since 7 September. R547 programs one compact-round challenge
to zero and obtains a proof, accepted by both verifier entry points, whose
committed trace fails checked extraction; R548 proves the algebra
(`reconstructed_eval_eq_iff_zero`, node S35): the reconstructed and true round
polynomials agree exactly at $x=0$. Under a uniform challenge this event has
probability about $1/p^4$ per round and belongs inside row 1; it has not been
charged (S23).

## 6. Stop condition

Rows 3 and 6 rest on a bound that does not exist at these parameters. Their
targets are valid only for a tuple family fixed before the challenge. The
unconditional replacement is refuted by item 4. The identified repair
(query-aware extraction with a pre-challenge target, or an explicitly charged
adaptive family; `decision.md` §§1–2) is described there as "genuinely new
mathematics". Rounds R1–R945 worked on privacy, native execution and source
refinement; no round note closes any part of S20, S21 or S22 (R19, R105
and R117 restate pre-beta extraction as open). With only the
bounds that are proved, the ledger total is at most 75.70 bits, and that
figure itself needs the missing quotient-to-batch bridge.

## 7. Gaps

1. **B1.** No coherent pre-$\gamma$ tuple list covering all accepting branches
   (S20). Rows 2, 3, 6, 7 depend on it.
2. **B2.** No pre-$\beta$ extraction of the quotient pair (S21). Rows 4, 5, 8,
   9 depend on it. New since 7 September.
3. **B3.** No bound on far-final accepted executions (S22).
4. **B4.** The only proved bounds for rows 3 and 6 are 75.74 and 80.90 bits,
   and they need a quotient-to-batch bridge that is not in the tree.
5. **B5.** Row 1 is the V7 inventory, not re-derived for R102; the zero-challenge
   rejoin event is uncharged; witness extraction from correct coefficients is
   not proved (S10, S23).
6. **B6.** No Fiat–Shamir theorem for the R102 transcript (S03); the BCS
   hypotheses are unchecked; the 100-bit reading (ii) is unreachable with a
   compiler linear in $Q$.
7. **B7.** List caps are V7 theorems for V7 objects, not rebound (S24); the
   tree gives both 100/99 and 112/113.
8. **B8.** The V8 soundness lemmas of early September (fixed-family scalar
   fingerprint, joint image game, fixed-target query lemma) are on other
   branches; none is in the tree at this base.
9. **B9.** Exact-source refinement of the transported weights, chord
   transpose and channel residuals (S02, deferred).
10. **B10.** Literature status of the cited published bounds was not
    re-fetched in this audit.
