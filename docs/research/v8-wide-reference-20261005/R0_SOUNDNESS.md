# R0: a reference design and paper proof of 100-bit soundness without grinding

2026-10-05. Research note. No verifier, prover, protocol or parameter of any
existing profile is changed. Written for a mathematician who has not read the
repository. Every step cites a Lean theorem in the tree, a published result,
or is marked NEW ARGUMENT.

**Verdict: HOLDS-ON-PAPER for the opening-layer theorem (§5), conditional on
the structural facts of §3. The end-to-end claim is CONDITIONAL on two named
premises: the semantic-layer bound (SEM) and Fiat–Shamir compilation (FS).**
With both, the round-by-round errors sum to $2^{-104.27}$ at 22 queries and
$2^{-105.40}$ at 24. Twelve gaps are listed in §9. This note has not been
reviewed.

## 1. What is claimed

"100 bits" is the repository's existing convention with the work set to zero:
the sum of the round-by-round knowledge errors is at most $0.7\cdot2^{-100}$
(`SECURITY.md`, V5 endpoint). A prover making $Q$ oracle queries then succeeds
without a witness with probability at most $Q$ times that, plus hash terms.
No error is divided by a work factor.

R0 is deliberately uncompressed. It is the ancestor that later optimisations
must be shown to preserve (§8). Size and compute are not constraints here.

## 2. The reference protocol R0

**Fields.** $\mathbb F=\mathbb F_p$, $p=2^{31}-1$. $K=\mathbb F_{p^4}$ (QM31,
$u^2=2+i$). $\mathbb E=K[v]/(v^2-u)$, of size $p^8\approx2^{248}$; `fields.py`
in `v8-wide-field-screen-20261005/` checks that $u$ is a non-square in $K$.

**Codes.** $D$ is the circle evaluation domain, $|D|=N=2^{20}$, partitioned
into $T=2^{18}$ fibres of four points; $D'$ is the fold domain, $|D'|=T$.
$\mathrm{Enc}:K^{1024}\to K^{D}$ is the injective linear encoder of the
current profile (the circle encoder composed with the R16 basis transport),
with image $\mathcal C$. $\mathrm{Fin}:K^{256}\to K^{D'}$ is the final encoder.
Both extend to $\mathbb E$ by the same matrices. A coefficient vector
$q\in K^{1024}$ is indexed $q_{d,s}$, $d<256$, $s<4$.

**Fold.** For a word $f$ on $D$ and a scalar $\alpha$,
$\mathrm{Fold}_\alpha(f)(u)=\sum_{s<4}\alpha^s\,\varphi_s(f|_u)$, where
$\varphi=(\varphi_0,\dots,\varphi_3)$ is a fixed invertible linear map on the
four values of each fibre $u$.

**Chord.** For distinct points $z_0,z_1$ of the circle over $K$ that are not
$\mathbb F$-rational, $L$ is the line through them; it has no zero on $D$.
For claimed values $y=(y_0,y_1)$, $I_y\in\mathcal C$ is the fixed degree-one
interpolant, linear in $y$.

**Protocol.** 29 lanes: 26 over $\mathbb F$ (commitment C1), 3 over $K$ (C2).

1. The prover commits words $W_l:D\to\mathbb F$, $l<26$. The verifier sends
   $\lambda,\chi\in K$. The prover commits $W_{26},W_{27},W_{28}:D\to K$.
2. Semantic phase over $K$, as in the V8 baseline before R17 (plain $G$; one
   channel). It ends with three points $P_1,P_2,P_3\in K^{10}$ and 87 claims
   $y^{\rm pt}_{j,l}$ for the multilinear evaluation of the message of lane
   $l$ at $P_j$.
3. The verifier sends $z_0$; the prover sends $y_{0,l}\in K$, $l<29$. The
   verifier sends $z_1\ne z_0$; the prover sends $y_{1,l}$.
4. The verifier sends $\gamma\in\mathbb E\setminus\{0\}$.
5. The prover sends $v\in\mathbb E$ (the claimed sum of the batched message
   over the 810 copy-inactive rows). The verifier sends $\kappa\in\mathbb E$,
   then $\tau\in\mathbb E$.
6. The prover sends a polynomial $P\in\mathbb E[X]$ of degree at most 6 by six
   coefficients; the verifier reconstructs $c_4$ so that
   $c_0+c_4=\tfrac14\,\mathrm{claim}'$ (defined below).
7. The verifier sends $\alpha_0\in\mathbb E$. The prover sends
   $F\in\mathbb E^{256}$.
8. The verifier sends a uniform set $S$ of $q$ distinct fibres. The prover
   opens all 29 lanes on the four points of each fibre, with authentication.

**Verifier.** Define the virtual lanes and batch

$$R_l=\frac{W_l-I_{y_{\cdot,l}}}{L},\qquad R_\gamma=\sum_{l<29}\gamma^lR_l,$$

the weights $w_\kappa=\kappa\,\mathrm{eq}(P_1)+\kappa^2\mathrm{eq}(P_2)+\kappa^3\mathrm{eq}(P_3)+\mathbf 1_I$,
the claim $\mathrm{claim}_\kappa=\sum_j\kappa^j\sum_l\gamma^ly^{\rm pt}_{j,l}+v$,
and $\mathrm{claim}'=\mathrm{claim}_\kappa-\langle w_\kappa,\mathrm{msg}(I_\gamma)\rangle$
with $I_\gamma=\sum_l\gamma^lI_{y_{\cdot,l}}$. Let $w^{\rm q}_\kappa$ be the
quotient weights of $w_\kappa$ (fact F6) and
$w_{\rm tot}=w^{\rm q}_\kappa+\tau e_1+\tau^2e_2$ with $e_1,e_2$ the image
functionals (F6). The verifier accepts iff the semantic checks pass, the
openings authenticate, and

- (V1) for every $u\in S$: $\mathrm{Fin}(F)(u)=\mathrm{Fold}_{\alpha_0}(R_\gamma)(u)$;
- (V2) $P(\alpha_0)=\tfrac14\langle F,\mathrm{DualFold}_{\alpha_0}(w_{\rm tot})\rangle$, where
  $\mathrm{DualFold}_\alpha(w)(d)=\sum_{t<4}w_{d,t}\,\alpha^{(4-t)\bmod 4}$ is the unscaled
  `dualFold` of `R370KernelEvaluation`; the quarter is written explicitly.

**Differences from R102.** $\gamma,\kappa,\tau,\alpha_0$, $v$, $P$ and $F$
are over $\mathbb E$. $G$ is a plain lane and there is one channel, so no
$\beta$ and no channel coefficients. (V1) and (V2) are checked directly: no
$\rho$ batching, no query injection, no relation rounds 1–3. The commitment
arity is immaterial. Everything through step 3 is the present protocol.

## 3. Facts used

Parameters: thresholds 38229 symbols and 9557 fibres; caps
$a_\gamma=336869026605739$, $a_f=9396508281246$.

- **F1 (initial agreement).** `exactV7InitialWidth29CurveDecodable`
  (`AspisFormal/K1/V7ExactCorrelatedAgreementInitial.lean`) proves
  `Width29CurveDecodable exactInitialEncoder 38229 initialBatchChallengeCap`.
  With `width29_bad_response_challenges_card_le`
  (`V6Width29CorrelatedAgreement.lean`): for any 29 lanes and any
  challenge-dependent choice of close codeword, at most $a_\gamma$ nonzero
  challenges admit a valid response with no matching decomposition. Proved
  over $K$; needed over $\mathbb E$ (gap 1).
- **F2 (fold agreement).** `exactV7FinalDegreeThreeCurveDecodable`
  (`V7ExactCorrelatedAgreementTerminal.lean`) proves
  `DegreeThreeCurveDecodable exactFinalEncoder 9557 foldChallengeCap`.
  `goodChallenges_card_le_of_no_jointAgreement`
  (`V5FriDegreeThreeCorrelatedAgreement.lean`) gives the no-joint-agreement
  form. The matched form is derived in step 6 (gap 2).
- **F3 (list size).** At agreement at least 38230 the initial code has at
  most 100 codewords around any word (V7 exact multiplicity-three
  Guruswami–Sudan caps; record
  `v7-exact-multiplicity-three-gs-audit-20260827.md`; `baseline.md` gives
  100 and 99). Gap 5.
- **F4 (fold of a codeword).** $\varphi_s(\mathrm{Enc}(q)|_u)=\mathrm{Fin}(q_{\cdot,s})(u)$,
  hence $\mathrm{Fold}_\alpha(\mathrm{Enc}(q))=\mathrm{Fin}(\sum_s\alpha^sq_{\cdot,s})$,
  and $\varphi$ is invertible on each fibre. Lean, natural-basis model:
  `fold_channels` (`AspisV8R16/FinalConsistency.lean`), `four_slot_inverse`
  (`AspisV8R16/FibreInterpolation.lean`), `firstFold`
  (`AspisV8R19/R370KernelEvaluation.lean`). **Lean over the exact encoders:**
  `AspisR0.Fold.F4`, `AspisR0.Fold.wideF4` (`lean/R0/Fold.lean`);
  F4 portion of gap 4 closed, compiled 2026-10-06.
- **F5 (round polynomial).** For $q,w\in\mathbb E^{1024}$ let $P_{q,w}$ be
  the degree-6 polynomial with coefficients $c_k(q,w)$. Then
  $P_{q,w}(\alpha)=\tfrac14\langle\mathrm{Fold}_\alpha q,\mathrm{DualFold}_\alpha w\rangle$
  and $c_0+c_4=\tfrac14\langle q,w\rangle$. Lean: `kernel_eval_pairing`
  (`R370KernelEvaluation.lean`), `coefficient_boundary`
  (`R653SourceCoefficientBoundary`). **OPEN: normalisation finding, gap 13.**
  `AspisR0.RoundNormalization.wide_unscaled_F5_counterexample` refutes the
  displayed evaluation equality when `DualFold` means the cited unscaled
  `dualFold`; F5 is not marked proved.
- **F6 (image and pairing).** There are linear functionals $e_1,e_2$ on
  $\mathbb E^{1024}$, depending only on the chord, with
  $L\cdot\mathrm{Enc}(q)\in\mathcal C\iff e_1(q)=e_2(q)=0$; and for such $q$,
  $\langle w,\mathrm{msg}(L\cdot\mathrm{Enc}(q))\rangle=\langle w^{\rm q},q\rangle$.
  Lean pieces: `sourceChord_last` (`R727TopBalance.lean`),
  `ordinary_source_boundary_of_image_tails` (`R896`),
  `source_chord_transpose_pairing`, `inverseTransport_dot`
  (`AspisV8R16/TransportDual.lean`), `original_weights_transported_pairing`
  (`AspisV8R17/SourceOriginalWeights.lean`). Gap 3.
- **F7 (distance).** Two distinct codewords of $\mathcal C$ agree on at most
  1024 points of $D$ (V7 exact GRS conversion; `decision.md` §1 uses the same
  root bound).
- **F8 (root count).** A nonzero vector of 29 values is annihilated by at
  most 28 batching challenges: `width29_nonzero_collision_card_le`
  (`V6Width29CorrelatedAgreement.lean`).

## 4. Attempts to break it

1. **The 7 September full-fibre construction** (zero on 9557 common fibres, a
   product polynomial elsewhere). It yields 7,072,436 values of $\gamma$ at
   which the batch is close to the zero codeword with no jointly close
   tuple. These are unmatched responses in the sense of step 2. They are
   counted, not excluded: $7072436\le a_\gamma$. Over $\mathbb E$ their
   probability is $2^{-225.3}$. No contradiction.
2. **A different close codeword for every $\gamma$.** The adversary may pick
   any candidate per challenge. F1 is stated for challenge-dependent
   strategies and bounds exactly this.
3. **A final vector that is close but is not the fold of a close
   codeword.** Bounded by the matched form of F2 (step 6).
4. **A quotient outside the code image** ($L\cdot\mathrm{Enc}(q)\notin\mathcal C$).
   Caught by $\tau$ (step 5) and by $\gamma$ per lane (step 3).
5. **Subfield structure.** Lanes are $K$-valued and $\gamma\in\mathbb E$.
   An $\mathbb E$-word is close to an $\mathbb E$-codeword on a set iff both
   $K$-components are, on that set. No shortcut found; step 7 shows the
   extracted codewords are $K$-valued.
6. **Degenerate challenges.** $\gamma=0$ is excluded by sampling. Every other
   special value ($\alpha_0=0$, $\tau=0$, roots of unity) is one element of
   a counted bad set or harmless; no step divides by a challenge.
7. **Claims chosen after seeing challenges.** Every bad set below is fixed by
   the transcript before its challenge.

Nothing found. That is not a proof of absence.

## 5. The opening-layer theorem

**2026-10-06 formalisation finding:** the F5/(V2) comparison after step 6 is incomplete as written, and false with the cited unscaled dual fold; see gap 13.

Fix the committed words $W=(W_l)$. For a word $f$ on $D$ write
$\mathrm{Close}(f)=\{q:\mathrm{Enc}(q)\text{ agrees with }f\text{ on}\ge38230\text{ points}\}$.
Let $\Lambda$ be the set of tuples $t=(c_l)\in\mathcal C^{29}$ that agree
with $W$ jointly on at least 38230 points, and, once $y$ is fixed,
$\Lambda_R$ the set of tuples $(q_l)$ with $\mathrm{Enc}(q_l)=R_l$ jointly on
at least 38230 points.

**Step 1 (lists).** $|\mathrm{Close}(f)|\le100$ by F3.
$|\Lambda|\le100$ and $|\Lambda_R|\le100$. NEW ARGUMENT: given 101 distinct
tuples, pick $\gamma^*\ne0$ outside the at most $\binom{101}{2}\cdot28=141400$
roots (F8) at which two of them have equal batches; the 101 batches are
distinct codewords, each agreeing with the $\gamma^*$-batch of the lanes on
at least 38230 points, contradicting F3.

**Step 2 ($\gamma$: every close codeword is explained).** A *valid response*
at $\gamma$ is a pair $(q,A)$, $|A|\ge38230$, with $R_\gamma=\mathrm{Enc}(q)$
on $A$. It is *matched* if some $(q_l)$ has $A$ inside its joint agreement
set with the lanes $R_l$ and $q=\sum_l\gamma^lq_l$. Let
$\mathcal B_1=\{\gamma\ne0:\text{some valid response is unmatched}\}$. By F1,
applied to a strategy that selects an unmatched response at each
$\gamma\in\mathcal B_1$, $|\mathcal B_1|\le a_\gamma$. A matched response
has $(q_l)\in\Lambda_R$.

**Step 3 ($\gamma$: per-lane image and claims).** For $t\in\Lambda$ let
$\delta_{j,l}(t)=y^{\rm pt}_{j,l}-\mathrm{eq}(P_j)\cdot\mathrm{msg}(c_l)$.
Let $\mathcal B_2$ be the set of $\gamma$ with
$\sum_l\gamma^le_i(q_l)=0$ for some $(q_l)\in\Lambda_R$ and $i$ with
$(e_i(q_l))_l\ne0$; let $\mathcal B_3$ be the set of $\gamma$ with
$\sum_l\gamma^l\delta_{j,l}(t)=0$ for some $t\in\Lambda$ and $j$ with
$(\delta_{j,l}(t))_l\ne0$. By F8 and step 1,
$|\mathcal B_2|\le100\cdot2\cdot28$ and $|\mathcal B_3|\le100\cdot3\cdot28$.
Both are fixed before $\gamma$.

**Step 4 ($\kappa$).** After $\gamma$ and $v$, for $t\in\Lambda$ put
$d_j=\sum_l\gamma^l\delta_{j,l}(t)$ and $d_I=v-\sum_{r\in I}\mathrm{msg}(c_\gamma)_r$.
$\mathcal B_4$ is the set of $\kappa$ with $\kappa d_1+\kappa^2d_2+\kappa^3d_3+d_I=0$
for some $t$ with $(d_1,d_2,d_3)\ne0$. $|\mathcal B_4|\le300$.

**Step 5 ($\tau$).** $\mathrm{Close}(R_\gamma)$ and $\mathrm{claim}'$ are
fixed before $\tau$. $\mathcal B_5$ is the set of $\tau$ with
$\langle w^{\rm q}_\kappa,q\rangle-\mathrm{claim}'+\tau e_1(q)+\tau^2e_2(q)=0$
for some $q\in\mathrm{Close}(R_\gamma)$ for which the three coefficients are
not all zero. $|\mathcal B_5|\le200$.

**Step 6 ($\alpha_0$).** Let $g_s=\varphi_s(R_\gamma)$, four words on $D'$,
fixed before $\alpha_0$. A valid response at $\alpha$ is $(F,M)$,
$|M|\ge9558$, with $\mathrm{Fin}(F)=\sum_s\alpha^sg_s$ on $M$; it is matched
if some $(F_s)$ has $M$ inside its joint agreement set with $(g_s)$ and
$F=\sum_s\alpha^sF_s$. Let $\mathcal B_6$ be the set of $\alpha$ with an
unmatched valid response. $|\mathcal B_6|\le a_f$: NEW ARGUMENT, the proof of
`width29_bad_response_challenges_card_le` applied verbatim to
`DegreeThreeCurveDecodable` (F2). For a matched response put
$q=(F_s)_s$. On each fibre of $M$ all four $g_s$ agree with
$\mathrm{Fin}(F_s)$, so by F4 $R_\gamma=\mathrm{Enc}(q)$ on $4|M|\ge38232$
points: $q\in\mathrm{Close}(R_\gamma)$ and $F=\mathrm{Fold}_{\alpha}(q)$.
Let $\mathcal B_7$ be the set of $\alpha$ with $P(\alpha)=P_{q,w_{\rm tot}}(\alpha)$
for some $q\in\mathrm{Close}(R_\gamma)$ with $P\ne P_{q,w_{\rm tot}}$.
$|\mathcal B_7|\le600$.

**Step 7 (queries).** Let $M_F=\{u:\mathrm{Fin}(F)(u)=\mathrm{Fold}_{\alpha_0}(R_\gamma)(u)\}$.
If $|M_F|\le9557$ then $\Pr[S\subseteq M_F]\le\binom{9557}{q}/\binom{T}{q}$.
The sampler's law: `uniform_success` (`AspisV8R19/R417Q22SuccessLaw.lean`,
for $q=22$).

**Theorem.** Suppose the verifier accepts, no challenge lies in its bad set
($\gamma\notin\mathcal B_1\cup\mathcal B_2\cup\mathcal B_3$,
$\kappa\notin\mathcal B_4$, $\tau\notin\mathcal B_5$,
$\alpha_0\notin\mathcal B_6\cup\mathcal B_7$) and $|M_F|\ge9558$. Then there
is $t=(c_l)\in\Lambda$ such that $c_l(z_j)=y_{j,l}$ for all $j,l$, all 87
point claims are true for $t$, and $v$ is the true inactive sum of its batch.
Moreover $c_l$ is $\mathbb F$-valued for $l<26$ and $K$-valued for $l\ge26$.

*Proof.* (V1) gives $S\subseteq M_F$, and $(F,M_F)$ is a valid response at
$\alpha_0$; by step 6 it is matched, so $F=\mathrm{Fold}_{\alpha_0}(q)$ with
$q\in\mathrm{Close}(R_\gamma)$. By (V2) and F5,
$P(\alpha_0)=P_{q,w_{\rm tot}}(\alpha_0)$, so $P=P_{q,w_{\rm tot}}$
($\alpha_0\notin\mathcal B_7$). Comparing $c_0+c_4$ (F5):
$\langle w_{\rm tot},q\rangle=\mathrm{claim}'$. By step 5,
$e_1(q)=e_2(q)=0$ and $\langle w^{\rm q}_\kappa,q\rangle=\mathrm{claim}'$.
The pair $(q,\text{its agreement set})$ is a valid response at $\gamma$; by
step 2, $q=\sum\gamma^lq_l$ with $(q_l)\in\Lambda_R$. Then
$\sum\gamma^le_i(q_l)=0$, so by step 3 every $e_i(q_l)=0$, and by F6
$c_l:=L\cdot\mathrm{Enc}(q_l)+I_{y_{\cdot,l}}\in\mathcal C$. $W_l=c_l$ on the
joint set, so $t\in\Lambda$; $c_l(z_j)=y_{j,l}$ because $L(z_j)=0$. By F6,
$\langle w_\kappa,\mathrm{msg}(c_\gamma)\rangle=\mathrm{claim}_\kappa$, i.e.
$\kappa d_1+\kappa^2d_2+\kappa^3d_3+d_I=0$; by step 4 all $d_j=0$ and
$d_I=0$; by step 3 all $\delta_{j,l}=0$. For the field of definition: a
Galois conjugate of $c_l$ is a codeword agreeing with $c_l$ on more than
1024 points, hence equal (F7). $\square$

The 7 September open classes: *no close anchor* is step 2 with
$\Lambda_R=\emptyset$; *far final* is step 7; *good anchor, same final* does
not arise, because the object extracted is $\Lambda$, fixed before any
challenge, and steps 5–6 tie the accepted $F$ to it.

## 6. Round-by-round ledger

State function: a prefix is *not doomed* iff some $t\in\Lambda$ is still
alive (a witness tuple, or one whose claims so far are all true) or some
earlier challenge fell in its bad set. By the theorem a doomed complete
transcript is rejected.

| Round | Bad set | Error | Bits |
|---|---|---|---:|
| Semantic phase | premise SEM | $396430/(\lvert K\rvert-1)$ | 105.40 |
| $\gamma$ | $\mathcal B_1\cup\mathcal B_2\cup\mathcal B_3$ | $(a_\gamma+14000)/(\lvert\mathbb E\rvert-1)$ | 199.74 |
| $\kappa$ | $\mathcal B_4$ | $300/\lvert\mathbb E\rvert$ | 239.77 |
| $\tau$ | $\mathcal B_5$ | $200/\lvert\mathbb E\rvert$ | 240.36 |
| $\alpha_0$ | $\mathcal B_6\cup\mathcal B_7$ | $(a_f+600)/\lvert\mathbb E\rvert$ | 204.90 |
| Queries, $q=22$ | $S\subseteq M_F$, $\lvert M_F\rvert\le9557$ | $\binom{9557}{22}/\binom{262144}{22}$ | 105.14 |
| Queries, $q=24$ | | | 114.70 |

Sum: $2^{-104.27}$ at $q=22$ (largest single round $2^{-105.14}$);
$2^{-105.40}$ at $q=24$. Both are below $0.7\cdot2^{-100}=2^{-100.51}$.

The same protocol with $\gamma,\alpha_0\in K$ gives 75.74 and 80.90 bits in
those two rows. That is the whole reason for $\mathbb E$. With
$\kappa,\tau\in K$ their rows are 115.8 and 116.4 bits, which would also do.

## 7. From the theorem to knowledge soundness

1. **Extraction.** In the random-oracle model the words $W_l$ are read from
   the prover's hash queries at the time each root is fixed; opened values
   are bound to them (`depth6_leaf_path_binding`,
   `AspisV8R19/R552Merkle8LeafPathBinding.lean`, for the eight-way tree; V7
   K1.2 for the binary tree). The extractor computes $\Lambda$ and outputs
   the witness of a $t\in\Lambda$ that has one.
2. **Premise SEM.** If no $t\in\Lambda$ extends to a valid payment witness,
   the probability that the semantic verifier accepts and some $t\in\Lambda$
   has all 87 point claims true is at most $396430/(|K|-1)$. Source:
   `V7K15FailureRootInventory` (Lean, V7 relation, list factor 100 included).
3. **Combination.** If no $t\in\Lambda$ is a witness tuple, acceptance
   requires a semantic bad event, a bad challenge of §5, or a bad query set.
4. **Premise FS.** Compilation of a round-by-round knowledge-sound IOP in the
   random-oracle model loses a factor $Q$ on the largest round error plus
   $O(Q^2/2^{208})$ (Ben-Sasson, Chiesa, Spooner, TCC 2016-B; Chiesa and
   Yogev 2024; for FRI-type protocols Block, Garreta, Katz, Thaler, Tiwari,
   Zając, ASIACRYPT 2023). Parameter check not done; cited from memory.

## 8. What each later optimisation must prove

| Step | Change | Obligation | In the tree |
|---|---|---|---|
| 1 | Batch the $q$ query equations with $\rho$ and inject them into the relation | root count, adds $q/\lvert\mathbb E\rvert$ | `badCombinedChallenges_card` |
| 2 | Relation rounds 1–3 in place of the direct dot product in (V2) | three degree-6 rounds, adds $18/\lvert\mathbb E\rvert$ | V7 has the analogue |
| 3 | Eight-way Merkle | binding | proved (R552) |
| 4 | Two-swap order | same codebook; dual weights | `inverse_transport`, `inverseTransport_dot` |
| 5 | Sparse-coded $G$ and a second channel | a second tested word; the joint list must not become a product of two lists, or SEM's factor 100 becomes $10^4$ and the semantic row falls to about 98.8 bits | not addressed |
| 6 | Channel fold | identity plus two roots per candidate pair | `quadratic_dot_product` |
| 7 | Native kernels | source refinement | deferred |
| 8 | Narrow $\kappa,\tau$ to $K$; 24 to 22 queries | re-evaluate the ledger | arithmetic |

Step 5 is the one that is not routine.

## 9. Gaps

1. **CLOSED (Replay 2026-10-06):** F1 and F2 over $\mathbb E$ are
   `AspisWide.Instances.wideInitialWidth29CurveDecodable` and
   `AspisWide.Instances.wideFinalDegreeThreeCurveDecodable`, for the exact
   encoders and unchanged thresholds/caps.
2. **CLOSED (Replay 2026-10-06):** the matched form of F2 is
   `AspisWide.MatchedInstances.wideFinal_bad_response_challenges_card_le`;
   `final_matchingDecomposition_iff` identifies the message-level match.
3. F6 as one statement (the image equivalence and the pairing with the
   interpolant correction) is assembled here from several Lean lemmas about
   the source-shaped weights; no single theorem states it.
4. **PARTLY CLOSED (2026-10-06):** F4 for the exact encoders is
   `AspisR0.Fold.F4` / `AspisR0.Fold.wideF4`. F5 remains open because of
   gap 13; the cited normalisation is audited by
   `AspisR0.RoundNormalization.cited_round_identities` and
   `AspisR0.CitedKernelAudit.literal_cited_kernel`.
5. **CLOSED (Replay 2026-10-06):** F3 is
   `AspisWide.MultiplicityThreeGS.exactInitialCloseCandidate_card_lt_101`;
   the joint-list bound is
   `AspisWide.JointList.jointInitialList_card_le_100` (messages) and
   `jointInitialCodewords_card_le_100` (codewords), with WideExact instances.
6. SEM is V7's inventory. It is not re-derived for R0's semantic layer (V8
   positive-transfer adapter, point-claim layout), and it contains three
   small V7 opening-layer terms that §5 counts separately.
7. FS: no theorem in the tree covers this transcript. V7's K1.6 compiler is
   specific to the V7 transcript, and its stage probability bounds were
   recorded as open on 14 September. A protocol-generic version is needed
   and would serve V7 as well.
8. R0 is defined in this note. Its agreement with the V8 baseline source up
   to step 3, the order of $\tau$, the exact interpolant and the role of the
   inactive claim were taken from research notes, not from source.
9. Samplers for $\mathbb E$ do not exist. The ledger assumes exactly uniform
   challenges conditional on no exhaustion.
10. The extractor's running time (list decoding 29 interleaved words) is not
    analysed.
11. Privacy is not addressed. Every disclosure after $\gamma$ doubles in
    size over $K$; mask capacity must be re-derived before R0 is frozen.
12. No published result was re-fetched, and this argument has had no
    review.
13. **F5/(V2) quarter normalisation (found 2026-10-06; resolved below).** The paper
    does not define `DualFold`. The cited `R370KernelEvaluation.dualFold`
    is unscaled, and `kernel_eval_pairing` states
    `P_{q,w}(alpha) = (1/4) * dot(firstFold q, dualFold w)`, with the
    same quarter used in `c0+c4 = (1/4) * dot(q,w)`. For `q=w=e0`,
    the first value is `1/4` and the unscaled pairing is `1`, for every
    alpha, including over WideExact. Compiled witnesses:
    `AspisR0.RoundNormalization.wide_unscaled_F5_counterexample` and
    `AspisR0.CitedKernelAudit.literal_cited_counterexample`. The precise
    stopped inference is “By (V2) and F5” in the proof after step 6:
    `comparison_step_counterexample` has claimed polynomial `1` and
    claim-prime `4`, satisfying the local (V2) and reconstruction equation,
    but failing the evaluation equality needed for B7. This is a local
    inference counterexample, not a complete accepting R0 transcript.
    The smallest specification addition that makes this comparison
    provable is to define the paper's `DualFold` as `(1/4)` times the
    cited `dualFold`. Alternatively, if the unscaled dual is intended,
    (V2) needs the factor `1/4`. Neither change has been made. No extra
    challenge exclusion or new premise has been inserted. The requested
    stop condition is reached; F6 and the remaining Part B formalisation
    are not claimed complete. See PORT_LOG.md, “R0 structural audit and
    stop finding 2026-10-06”.

    **Resolved 2026-10-06 by specification correction (owner decision).** The
    quarter belongs on both identities, as `kernel_eval_pairing` states; F5 and
    (V2) above now carry it. The inference after step 6 is unchanged: (V2)
    gives $P(\alpha_0)=P_{q,w_{\rm tot}}(\alpha_0)$, hence $P=P_{q,w_{\rm tot}}$,
    hence $\tfrac14\langle w_{\rm tot},q\rangle=c_0+c_4=\tfrac14\,\mathrm{claim}'$.
    The cited counterexamples refute the earlier unscaled statement only.