# Future version: soundness rows for the changed verifier

> **Correction, 2026-11-11.** Two statements below are wrong as descriptions of the pinned
> theorem: that a bound "of the pinned form ... keeps its largest row" when rows are added, and
> the implication that the seven new rows cost about `2^-120.3` in the composed bound. The
> pinned bound charges every transcript start a common envelope `B = 15/2^109` and holds
> `34·B < 2^-100` with a margin of `2/2^109`. Seven more starts give about `1.2 · 2^-100`, so
> under the pinned accounting this verifier misses criterion (A) of the contract. A per-row
> accounting would be a different composition theorem and does not exist. See
> `V8-LESSONS-CHECK.md`, finding 1. The per-row caps below stand as per-row caps only.

Status: accounting sketch for the experiment on branch `future-version`.
Nothing here is proved except where a Lean theorem is named. It states what
would have to be proved, in the row form of
`docs/research/v8-r1-20261011/R1_SOUNDNESS.md`, so that the changes can be
judged before more is built on them. The release target is unchanged and not
yet established; these changes add obligations to it.

The pinned record has 33 Fiat-Shamir rows (0 to 32) and a bound of the form
`Qtot * (largest row) + collision term`, with the query row the largest at
about `2^-105.14`. `K` is QM31, `|K| = (2^31 - 1)^4`, and `E` is WideExact.
A challenge drawn in `K` by the block sampler `qm31_sample` lands in a fixed
set `B` with probability at most `|B| * ceil(2^256 / |K|) / 2^256`, the form
the record uses for the `rho` row.

## What changes

| | Pinned verifier | Future verifier |
|---|---|---|
| First fold, per query `i` | `F_i = b_i` checked for each of the 22 queries | one equality `sum_i rho^i (F_i - b_i) = 0` (stage C) |
| Second fold and final polynomial | `sum_i rho^i (e_i - G_i) = 0` | the same quantity, as the claim `sum_j f_j w_j = rhs2` proved by sumcheck (stage D) |
| Relation pairing | `sum_j f_j W_j = claim` computed directly | the claim proved by the same sumcheck (stage D) |
| Transactions | two, joined by an authenticated checkpoint | one; no checkpoint |
| Merkle authentication | two multiproofs per tree (queries 0..10, 10..22) | one multiproof per tree over the 22 queries |
| Field arithmetic | pinned kernels | exact replacements (same values) |

Notation: `F_i` is the first fold of the gamma-combined opening of query `i`,
`b_i` the authenticated folded value it must equal, `G_i` the second fold,
`e_i = sum_j f_j b_j(x_i)` the final polynomial at the query's node, `f` the 64
final-message values, `W` the folded relation weight vector, and
`w_j = sum_i rho^i b_j(x_i)`.

## Stage C: the batched first fold

**Residuals.** `r0_i = F_i - b_i` and `r1_i = e_i - G_i`, for `i < 22`. Both
vectors are functions of the opened values at the queried positions (C1, C2
and folded leaves), of `gamma`, `alpha0`, `alpha1`, the final message and the
query positions. All of these precede `rho` in the transcript, except the
opened values, which are fixed by the three roots on the commitment-binding
hypothesis.

**Row `rho`, restated.** Bad set for a transcript prefix:
`bad2(r0, r1)`, the subfield roots of the residual polynomial of the first of
the two vectors that is not identically zero, and empty if both are zero.

- Proved (Lean, algebra only): `bad2_card_le_21`, and
  `all_zero_of_both_evals_zero_outside_bad2`: outside the bad set, the two
  batched equalities imply all 44 coordinate equalities
  (`lean/TwoFamilyResidualBatch.lean`).
- Cap: `21 * ceil(2^256 / |K|) / 2^256`, about `2^-119.6`, the pinned row's
  number. A second family at the same challenge does not double it.
- Consequence used downstream: off the bad event, an accepting run has every
  per-query residual zero, which is the hypothesis the pinned query row and
  the fold rows consume. Those rows are unchanged.

**What is new to prove.**

1. The row's hypotheses now include binding of the C1 and C2 trees, because
   `r0` reads their openings; the pinned row needs only the folded tree. The
   binding event itself is already charged once in the pinned argument, so no
   new numerical term is expected, but the bridge
   (`QueryResidualBridge` in the pinned development) has to be restated for
   the pair `(r0, r1)`.
2. The acceptance predicate is strictly larger than the pinned one: data with
   `r0 != 0` and `rho` in the bad set is accepted here and rejected by the
   pinned verifier. The test
   `rho_dependent_cancellation_passes_the_batched_check_and_fails_the_pinned_one`
   exhibits such data. Any statement of the form "the future verifier accepts
   exactly what the pinned verifier accepts" is false and must not be used.

## Stage D: one sumcheck over the final message

**Protocol.** After `rho`, on a transcript seeded from the post-`rho` state
(rows 33 to 39):

- Row 33 absorbs `claim` and `rhs2` (64 bytes) and yields `lambda` in `K`.
  `C_0 = claim + lambda * rhs2`, `u_j = W_j + lambda * w_j`.
- Rows 34 to 39: for `b = 0..5` the prover sends `(c0, c2)` in `E`, the
  constant and quadratic coefficients of
  `s_b(X) = sum over the unbound positions of f~ * u~`; the verifier sets the
  linear coefficient to `C_b - 2 c0 - c2`, draws `r_b` in `K` over those 64
  bytes, and sets `C_{b+1} = s_b(r_b)`.
- Final check: `C_6 = f~(r) * (W~(r) + lambda * w~(r))`, with the three
  multilinear extensions computed by the verifier.

**Rows.**

| Row | Bad event for a fixed prefix | Size of the bad set | Cap |
|---|---|---:|---|
| 33 (`lambda`) | exactly one of the two claims is false, or both are, and `lambda` makes the combination true: `(S_W - claim) + lambda (S_w - rhs2) = 0` with the bracket pair not both zero | at most 1 | `1 * ceil(2^256/|K|)/2^256` |
| 34 to 39 (`r_b`) | the prover's `s_b` differs from the true round polynomial and agrees with it at `r_b`; both have degree at most 2 | at most 2 each | `2 * ceil(2^256/|K|)/2^256` each |

Sum of the seven caps: `13 * ceil(2^256/|K|)/2^256`, about `2^-120.3`. Each is
below the largest pinned row, so a bound of the pinned form
`Qtot * (largest row) + collision` keeps its largest row; the row count
becomes 40 and the re-instance of the composition theorem has to carry it.

Here `S_W = sum_j f_j W_j` and `S_w = sum_j f_j w_j` are the true sums. They
are fixed before `lambda`: `f` is absorbed at row 31, `W` is a function of
challenges up to `alpha1` and of `kappa`, and `w` is a function of the queries
and `rho`. `claim` is a function of the transcript prefix; `rhs2` is a
function of the opened folded values, fixed by the folded root on the binding
hypothesis, and is absorbed at row 33 before `lambda` is drawn.

**What the stage establishes.** Off the seven bad events and the binding
event, acceptance implies `S_W = claim` and `S_w = rhs2`, which are the two
equalities the pinned verifier computes directly. `S_w = rhs2` is the batched
second-fold equality `sum_i rho^i (e_i - G_i) = 0` of stage C.

**What is new to prove.**

1. The seven rows in the adaptive argument, with the decoder `qm31_sample`
   for each (the pinned record lists the same decoder for `rho` as still to be
   fixed).
2. Round-by-round soundness of the six-round sumcheck over `E` with
   challenges in `K`: a nonzero polynomial of degree at most 2 over `E` has at
   most 2 roots in `K` (`subfield_roots_card_le_natDegree` covers this).
3. The verifier's three evaluators equal the multilinear extensions of the
   vectors they stand for: `f~` (a 64-term sum against the equality table),
   `W~` (`Weights::mle_at`: five product rows, the inactive row, the Libra
   row, combined with powers of `kappa`), `w~` (the per-query product form).
   Tested against direct sums over the explicit 64-entry vectors at Boolean
   and random points; not proved.
4. Canonical encoding of the twelve certificate values (non-canonical
   encodings are rejected at decode).
5. Privacy: the certificate is a deterministic function of the final message,
   the challenges and the opened folded values, all already in the adversary's
   view. A simulator that produces that view can compute the certificate from
   it. Stated, not proved; the per-proof privacy figure is unchanged if this
   holds.

## One transaction

The pinned two-transaction split carries an obligation of its own (stage 1's
checkpoint digest implies stage 2's assumptions). The future verifier has no
checkpoint, so that obligation is removed, not transferred. What replaces it
is the adapter's single entry: the statement reconstructed from the request
and the authenticated accounts is validated and the whole proof verified in
one invocation. The entry needs its own source-level statement.

## One multiproof per tree

A multiproof over the 22 query indices in the canonical node order, in a fixed
slot padded with zeros. No probabilistic row changes: the same leaves are
authenticated against the same roots with the same node grammar, and the
binding hypothesis is the one already used. What needs an argument is the slot
bound (below) and, as today, that the node count is a function of the index
set alone.

**Slot bounds.** For `n` distinct leaves in a binary tree with `2^k` nodes at
level `k`, at most `min(m, 2^k - m)` siblings are supplied at a level with
`m = min(n, 2^k)` occupied nodes, because a supplied sibling is an unoccupied
node whose sibling is occupied.

- C1 and C2 (depth 18, `n = 22`): levels 18 down to 6 give at most 22 each
  (286), level 5 gives at most `32 - 22 = 10`, higher levels give 0: 296.
- Folded tree (depth 18, indices below `2^16`, at most 22 distinct): the
  occupied nodes lie in the leftmost quarter. Levels 18 down to 8 give at most
  22 each (242), level 7 gives at most 10, and the two top levels need one
  sibling each: 254.

The same count gives the pinned slots (146 and 172 for 10 and 12 leaves, 128
and 150 for the folded tree). The bit-reversed index sets attain 296 and 254
(tested).

## Exact arithmetic changes

No row changes. Each is a claim that a function returns the same value as the
one it replaces, under a stated precondition (canonical limbs in every case).
The obligations are source-level equalities and no-overflow bounds for:
`QM31::mul` (sixteen-product form), `PreparedQm31Multiplier::mul`,
`QM31::square`, `QM31::mul_add`, validated-record decoding, the single-pass
and in-place Merkle traversals (result and error kind equal to the two-pass
form), the lazy boundary sum, and the stage C and stage D kernels on this
branch. Each has an equivalence test; none has a proof.

## Open decisions before any release claim

- Domain separation of the transcript by verifier version. The future
  verifier uses the pinned transcript for rows 0 to 32, so a pinned proof can
  be re-packed into the future format by anyone (new multiproofs and the
  certificate are functions of public data). That is convenient for testing
  and harmless for soundness as analysed here, but a release should decide
  whether the two versions share a transcript domain.
- Where the bound's row count and decoders are fixed (`p.rounds = 40`).
- The all-input cost argument for the one-transaction path.
