# The Aspis one-transaction verifier: soundness argument and open obligations

Status, 2026-11-11. Research note. "R1" means the existing two-transaction
verifier at the PIN2 pin; "the Aspis one-transaction verifier" means
`verify_summed_format` (crates/aspis-r1-cost-probe/src/fused.rs) at source
`8a4059c8bc2`, reached through the Pool adapter's settlement entry, in the
deployed feature set (`pool-adapter, future-one-tx-lean, private-leaf-salts,
future-fast-kmul, future-fast-prepared, future-fast-square,
future-validated-decode, future-merkle-single-pass, future-tight-base,
future-tight-weights, future-lazy-boundary, future-d-inactive-tensor,
future-d-pair-expansion, future-merkle-in-place, future-lazy-horner,
future-fold-shared`; evidence/future-version-20261111/out/A5-onetx-lean/cmd.txt).
Its three changes from R1, in plain words: the batched first-fold check (one
ρ-weighted equality in place of 22), the final sumcheck (a combining challenge
λ and six rounds in place of computing the two final inner products), and one
multiproof per tree; plus exact arithmetic replacements and no checkpoint.

The release target (100-bit classical security of the frozen two-transaction
R1 path) is unchanged and **not yet established**. Nothing here attaches it,
or any figure, to the Aspis one-transaction verifier. **For the Aspis
one-transaction verifier there is no per-attempt figure.** What exists is a
deterministic reduction to the R1 equalities (algebra proved in Lean, source
part open) and a list of open obligations, one of which (finding 1) decides
whether the R1 form of bound can be carried at all.

Correction recorded here (SOUNDNESS-ROWS.md is not edited; the lead marks it
superseded): its statements that the R1 bound "keeps its largest row" when the
seven rows are added and that "the row count becomes 40" with nothing else
changing are wrong for the theorem as proved. See finding 1.

## 0. Findings, most important first

### Finding 1: the R1 numeric form does not carry over (verified from the Lean source)

What the R1 bound charges, read from the source:

- `StartChargeProbability.restricted_union_bound` (lean/StartChargeProbability.lean:29)
  bounds the hit mass by `((Q+34 : Nat) : ℚ) * PerAttemptEnvelope.B`. It is
  `RawAdaptiveClassifierStartBound.shared_hit_mass_le_starts` (:18) applied
  with `N = Q+34`, which is `DecodedFirstReadUnionBound.decoded_first_read_bound`
  (:29) with `ε := PerAttemptEnvelope.B`.
- `decoded_first_read_bound` takes ONE density `ε` that must bound the bad
  mass of every decoded start (`hbad : ∀ a T own pend g, dec a T = some ... →
  blaw ... ≤ ε`) and a count `N` of decoded fresh first reads in the log
  (`DecoderReadsBound dec q t N`). Its conclusion is `N * ε`. It is uniform in
  ε: there is no per-row or per-kind version in the tree.
- N counts decoded first reads in the whole charged log, the adversary's and
  the verifier's sampler reads together: `StartChargePrefix.starts` proves
  `≤ Q + 34` as `starts_le_queries` (adversary, ≤ Q) plus
  `BinHonestQueryBudget.verifier_starts` (≤ 34). The 34 is
  `rows_bound` over `List.range 33` with one start per row and two at row 26
  (`sampler_starts`: `≤ 1 + if n = 26 then 1 else 0`), the row-26 sampler
  being the reseed into the opening transcript.
- `B = 15/2^109` (lean/PerAttemptEnvelope.lean:17), `34·B = 510/2^109`, and
  criterion (A), `total(0) < 2^-100`, holds with a margin of about `2/2^109`.

Starts of the Aspis one-transaction transcript, counted from the code: the
33 R1 rows and the R1 reseed (34), the fresh transcript start of the final
sumcheck, `Transcript::new(hash, p.state, S2)` (fused.rs:521), which has
exactly the frame form of the R1 reseed (1), the combining challenge (1) and
six round challenges (6): **42**, or 41 if the final sumcheck continued the
existing transcript instead of starting a new one.

At the common envelope:

| Starts at B | total(0) / 2^-100 |
|---|---|
| 34 (R1) | 0.996094 |
| 35 | 1.025391 (Lean `starts35_exceed`: 35·B > 2^-100) |
| 41 | 1.201172 |
| 42 | 1.230469 = 2^-99.70 |

(collision, account, abort and query-scan terms as in R1 in every line.) So,
under the R1 accounting, **the Aspis one-transaction verifier misses criterion
(A)**. No common envelope fixes it: B must cover the query row
(≈ 2^-105.14 ≈ 14.5/2^109) and `41 · 2^-105.14 > 2^-100`.

What theorem would be needed. A kind-indexed generalisation of
`decoded_first_read_bound`: given a decoder whose decoded starts carry a kind
`k` (the row), densities `ε_k ≥ 0` with every decoded start of kind k having
bad mass `≤ ε_k`, a bound `Q` on adversary first reads, and a bound `n_k` on
the verifier's own decoded first reads of kind k, conclude

```
hit mass ≤ Q · max_k ε_k + Σ_k n_k · ε_k.
```

Plus: a start count for the 40-row transcript split by kind and by source
(replacing `verifier_starts`), the decoder extended to rows 33–39 and to the
second fresh-start frame, and the per-kind densities (section 3). Two
instantiations, neither established:

- conservative (R1 rows still at B, the 8 new starts at the new rows' cap
  `2a ≈ 2^-123`): `total(0) ≈ 0.996095·2^-100`, margin `≈ 0.99975·2^-108`
  (Lean `perKind_margin`, arithmetic only);
- per row for every verifier start: `Q·B + Σ_rows cap`. From
  `SemanticBudget.roots` (25 semantic rows, root counts summing to 303,100,
  times `(1+δ)/|K|`) that sum is about `2^-105.8`, plus the query row
  `2^-105.14`, plus ρ, the new rows and the opening rows; the circle rows'
  caps were not read here. Roughly `Q·B + 1.6·B`, if the circle rows are
  small. Not established.

The lead's message gives 41 starts and "roughly Q·B + B"; the count here is 42
with the final sumcheck's fresh start, and the per-row sum is closer to 1.6·B
on the caps read. Neither changes the conclusion. Whether to prove the
kind-indexed theorem, and whether a bound derived that way may be published,
is an owner decision; the per-row figure is not presented as established.

### Finding 2: no attack on the new algebra was found

Every quantity a new bad set depends on is fixed, by an absorb or by a Merkle
root absorbed earlier, before the challenge the set concerns (section 2). The
composed algebraic statement is proved in Lean (`stageCD_sound`), as a model
theorem; its connection to the Rust is open.

### Finding 3: the composition instance is fixed at 33 rows

The generic `R0C.V3.theorem43` (v8-r0-close-20261007/lean/R0C/V3/Gen.lean:251)
is parametric in the protocol (`maxErr rb.ε pr.r`). Its R1 instance
`AspisR1.UnifiedFiatShamir.soundness_bound` takes `hl : ∀ n < 33, p.lbl n =
UnifiedLabels.label n` and concludes with `maxErr rb.ε 33`; `UnifiedSampler`
special-cases row 26 (reseed) and row 31 (queries). The 40-row transcript needs
its own protocol instance, decoder, classifier (D1/D2/D3) and start count.

### Independent review of findings 1 and 3 (soundness lead's reviewer, 2026-11-11)

A reviewer working for the soundness lead read the R1 Lean separately. Result, with its references:

- Finding 1 is confirmed. `F3T_Numeric.total` is `(Q+34)*B + collisionLoss + accountLoss + 2^-126
  + 2^-454`; `restricted_union_bound` (lean/Frozen2StartChargeProbability.lean:29-36) goes through
  `shared_hit_mass_le_starts` (RawAdaptiveClassifierStartBound.lean:18-36) to
  `decoded_first_read_bound` (DecodedFirstReadUnionBound.lean:29-35), which takes one scalar and
  concludes `N * eps`. The per-row budgets exist as definitions and are replaced by `B` at
  `LiteralBudgetEnvelope.row_le` (LiteralBudgetEnvelope.lean:40). `theorem43` and
  `combined_fiat_shamirZ` charge `Qtot * maxErr`, a maximum over rows (FS/Statement.lean:232).
- CORRECTION to finding 3. `verifier_starts` is not fixed at 33: it concludes at most 34
  (BinHonestQueryBudget.lean:104-111; row 26 is counted twice by `sampler_starts`).
  `UnifiedFiatShamir.soundness_bound` (UnifiedFiatShamir.lean:23-48) does carry the 33-row premise,
  but the headline `total` does not use it. The conclusion of finding 3 stands in this form: the
  headline's start count and its single density are both specific to R1's 33 rows.
- A per-kind accounting is new proof in three pieces: a weighted `decoded_first_read_bound` (a cap
  per start by decoded row, with a weighted start budget); a per-row density lemma that stops
  before `row_le`, which needs the decoded row fixed at each start because
  `RawUnifiedDecoder.decoded_bound` quantifies over all 33 rows; and a per-row replacement for the
  `Q+34` starts theorem. The adversary's `Q` starts still cost `B` each.
  `mean_firstHit_union_le` (CausalFirstHitUnionBound.lean:48) is a static union bound over a fixed
  index set and cannot stand in.
- Arithmetic from the definitions: row 31 alone is `0.967*B` (it sets `B`); the 33 R1 caps sum to
  about `1.58*B`, in line with the "roughly 1.6*B" above.

### Finding 4: the final sumcheck's fresh transcript start reuses the R1 frame

`H(domain ‖ tag ‖ p.state)` is byte-for-byte the form of the R1 reseed
`H(domain ‖ tag ‖ semantic_state)` (verifier.rs:86, transcript.rs:12), same
domain string and tag. Not a soundness break: in the random-oracle model the
two are distinguished by what produced the 32-byte state, and every later
frame of the final sumcheck has a row tag (0xc1..0xc7) no R1 row uses
(0xa0..0xc0). It costs one start (finding 1) and makes a decoder read the
frame two ways. Recommendation (a protocol change, not made): continue the
R1 transcript object instead of starting a new one, or give the final
sumcheck its own domain string. Rows 0 to 32 are byte-identical to R1, so R1
proofs re-pack into the one-transaction format; a release should decide
version separation of the transcript domain.

**Resolved in source, 2026-11-11 (owner decision "1 yes").** The final sumcheck now continues
the opening transcript (`Transcript::resume`, no start frame), and the proof format magic is
`ASPIS` + two zero bytes + format number 2. At the branch head the Aspis transcript therefore has
41 starts (34 as in R1 plus the seven new rows) and no frame that reads two ways. The verifier
deployed on devnet (source 8a4059c8bc2, magic `R1F1SM22`) is immutable and keeps the earlier
frame and 42 starts; its proofs and the new format's proofs are not valid for each other. No new
ELF has been built or measured for this change. Finding 1 is unaffected in kind: 41 starts at
the common envelope are `615/2^109`, about `1.2 · 2^-100`.

**Owner decision on the accounting, 2026-11-11 ("for 2 yes").** For Aspis, a bound proved by
charging each transcript start its own row's cap, with the adversary's `Q` starts still charged
the largest cap, is acceptable. It was put to the owner as: same adversary, same quantity, same
target, counted per step; the formula of the stated bound changes; nothing is quoted until it is
proved. The stated alternative was a 23rd query. The decision concerns Aspis only and changes
nothing in the R1 claim. It makes the three pieces listed in the independent review above the next
deliverable; none of them exists yet, and until they do Aspis has no per-attempt figure.

### Finding 5: envelopes

The verifier core issues at most 1,112 digest calls (section 6.3), below
R1's 1,161, so `collisionLoss(Q) = 6(Q+1161)^2/2^256` stays an upper bound
on R1's own conditions. The account term's 2,965 reads and the issued-call
count 2,322 come from the two-transaction account run; the one-transaction
adapter path has not been counted (missing input).

## 1. Security statement (intended, not established)

Same game, adversary and units as SOUNDNESS-CLAIM-DRAFT-20261108 section 1:
SHA-256 as a uniformly random function, arbitrary adaptive adversary, Q =
digest queries it issues (duplicates and calls before rejection counted),
failure = accepted and the extractor fails. Differences forced by the
implementation: one adversary phase and one entry execution; no checkpoint
account and no `Runs` clauses about it.

Criteria are the contract's (A) and (B) only. No other reading of "100 bits"
is used.

- Under the R1 accounting (uniform B): `total(Q) = (Q+42)·B + collisionLoss(Q)
  + accountLoss(Q) + 2^-126 + 2^-454`, which fails (A).
- Under a kind-indexed accounting that does not exist yet:
  `(Q+34)·B + 8·b + collisionLoss(Q) + accountLoss_1tx(Q) + 2^-126 + 2^-454`,
  `b = 2·⌈2^256/|K|⌉/2^256`, which would meet (A) if `accountLoss_1tx ≤
  accountLoss`.

Both need everything in section 9. No proof-of-work or grinding credit; no
division by work.

## 2. Challenge ledger (from the code)

`absorb(row, payload)` is `state ← H(state ‖ 0x00 ‖ (0xa0+row) ‖ len32 ‖
payload)`; `block` outputs `H(state ‖ 0x01)` and advances `state ← H(state ‖
0x02)` (transcript.rs:14–22). Each challenge binds everything absorbed before
it through the chained state.

| Row | Absorbed, in order | Challenge | Sampler |
|---|---|---|---|
| init | public statement bytes and the C1 root | — | — |
| 0–26 | semantic rows; C2 root in row 2 (R1 record: r1_wire.rs:179, :390; r1_semantic.rs:292, :314; not re-derived here; code unchanged except arithmetic features) | semantic, circle | R1 samplers |
| R1 reseed | `H(domain ‖ S2 ‖ semantic_state)` | — | — |
| 27 | y1, 29×32 logical bytes | γ ∈ E, nonzero | `gamma_sample` |
| 28 | inactive sum, 32 | κ ∈ E | `ordinary_sample` |
| 29 | first round polynomial, 7×32 | α0 ∈ E | `ordinary_sample` |
| 30 | folded root 32 ‖ second round polynomial 7×32 | α1 ∈ E | `ordinary_sample` |
| 31 | final message, 64×32 | 22 query indices | eight block pairs, `queries_from_pairs` |
| 32 | empty | ρ ∈ K | `qm31_sample` |
| fresh start | `H(domain ‖ S2 ‖ p.state)`, p.state = state after row 32 (verifier.rs:97, :101) | — | — |
| 33 | `claim ‖ rhs2`, 64 bytes (fused.rs:522, :555) | λ ∈ K | `qm31_sample` |
| 34+b, b = 0..5 | `c0_b ‖ c2_b`, the round's 64 certificate bytes, both decoded canonically first (fused.rs:526–529) | r_b ∈ K | `qm31_sample` |

Never absorbed: the 22 openings and all Merkle nodes. They are bound only by
the three roots: C1 (init), C2 (row 2), folded tree (row 30). All three
precede the queries (row 31) and ρ (row 32).

### 2.1 Bytes neither absorbed nor checked

Checked layout (compact.rs:37–47, fused.rs:712–745): bytes 0..8 magic
(checked), 8 variant (checked), 9..16 zero (checked); semantic, y1, inactive,
the two round polynomials, folded root, final message: absorbed (the compact
semantic and y1 sections through their expansion); each 832-byte opening:
C1 values with salt, C2 values with salt, folded values with salt, every byte
inside a leaf hash, so bound through a root; the three node slots: the
consumed prefix enters the parent hashes, the rest must be zero
(`merkle_verdict`); the certificate: all 384 bytes absorbed after canonical
decoding; the length is fixed. Outside the verifier, the
candidate-afterstate prefix of the proof buffer is decoded with a canonical
re-encode check by the adapter (r1_pool_adapter.rs:792–808). **No byte
found that is neither absorbed nor checked.** Confirms the lead's finding.

### 2.2 Statement fields outside the transcript

Verified by running the lead's test
`tests/aspis_one_tx_statement_binding.rs` (2 tests, pass; command in section
11): changes to 13 statement fields over six fixtures (69 cases) are rejected;
a change of the source sequence number is rejected by a guard; a change of the
source **current root** is accepted by the verifier function. Nothing in this
argument uses the current root: the verifier's soundness statement is about
the bytes the transcript absorbs. What needs it is the entry: the settled
statement must take the current root from the authenticated lane account, not
from prover data. The one-transaction entry rebuilds the lane snapshot from
that account before `reconstruct_asq8_statement`; a source statement saying
so is part of the open entry obligation (section 7).

### 2.3 Attack checklist

| Question | Answer from the code |
|---|---|
| `claim` and `rhs2` both absorbed before λ? | Yes, row 33's payload is exactly their 64 bytes. `claim` is a function of the absorbed prefix; `rhs2` depends on openings and is bound here explicitly. |
| Each round's (c0, c2) absorbed before r_b? | Yes, the round's 64 certificate bytes, decoded (non-canonical limbs rejected, wide_exact.rs:255) before the challenge is drawn. |
| Certificate bound to the post-ρ state? | Yes, the final sumcheck starts from `p.state`, the state after ρ's advance. |
| Bad-set inputs fixed before their challenge? | See section 3, column "fixed by". |
| Queries and final message fixed before ρ? | Yes: row 31 absorbs the final message and derives the queries; ρ is row 32. |
| W depends only on data before the final message? | Yes: `Weights::new(variant, semantic_alpha, z)` and α0, α1, κ (rows ≤ 30) (weights.rs:206; fused.rs:543–544). |
| Non-canonical certificate limbs | Rejected. No malleable encoding exists. |
| Round order vs evaluator bit order | Consistent: round b folds pairs `(2m, 2m+1)` (fused.rs:694–695), so binds bit b; `equality_tables` uses `r[b]` for bit b (:569–575); `digits[d]` uses bits `(2d, 2d+1)` against `factors[k][d+2]`, whose digit is `(j >> 2d) & 3` in `Weights::tensor`/`raw`; `query_weight_mle` multiplies `t_0..t_5`, `t_0` the query node, as `accumulate_weights` builds the basis. |
| Degree bound enforced by the (c0, c2) form? | Yes. The verifier never reads a linear coefficient; `s = c0 + c1 X + c2 X^2` with `c1 = C − c0 − c0 − c2` (Lean `proverPoly_eval` is the coded update `c0 + (c1 + c2 r) r`; `proverPoly_natDegree`, `proverPoly_sum`). The true round polynomial has degree ≤ 2 (`roundPoly_natDegree_le`). |
| E-valued polynomials, K-valued challenges | ≤ 2 roots in E, hence in `iota(K)` (`subfield_roots_card_le_natDegree`). Needs E a field: E = QM31[v]/(v^2 − u), u a non-square (`WideTower.lean:qm31_wideU_not_isSquare`, cited at wide_exact.rs:20); the Rust-to-field correspondence is R1's obligation, unchanged. |
| Is the final check the right identity? | `f_at·(w_at + λ q_at) = C_6`; by linearity of the iterated fold (`foldAll_add_mul`) and `foldAll_zero_eq_sum` this is the iterated fold of f times that of `u = W + λw`, provided each evaluator equals `Σ_j v_j eq_j(r)` (section 5). |
| Duplicate folded indices | Equal `u/4` must carry identical leaf hashes (fused.rs:776–780), as in R1. |

Retained teeth vector for the changed acceptance predicate: the existing test
`rho_dependent_cancellation_passes_the_batched_check_and_fails_the_pinned_one`.
The Aspis acceptance set strictly contains R1's; every statement below is
"accepted and no bad event", never "same acceptance".

## 3. New and changed rows

`a = ⌈2^256/|K|⌉/2^256`, the mass per element of `qm31_sample` (rank mod
P^4, sampler.rs:21–50); `a ≤ 1/|K| + 2^-256 ≈ 2^-124.0` (Lean `ceil_mass_le`).

| Row | Bad event for a fixed prefix | Fixed by, before which challenge | Size | Cap |
|---|---|---|---:|---|
| 32, batching challenge ρ (changed) | ρ is a K-root of `Σ r0_i T^i` if `r0 ≠ 0`, else of `Σ r1_i T^i` if `r1 ≠ 0` | `r0_i = F_i − b_i`: C1, C2 openings (roots: init, row 2), folded value (root: row 30), γ (27), α0 (29), query i (31). `r1_i = e_i − G_i`: final message and query nodes (31), α1 (30), folded openings (row 30 root). All before ρ (32); the openings only through Merkle binding. | ≤ 21 (`bad2_card_le_21`) | `21a ≈ 2^-119.61` (R1's number) |
| 33, combining challenge λ (new) | `(S_W − claim, S_w − rhs2) ≠ (0,0)` and `(S_W − claim) + λ(S_w − rhs2) = 0` | `S_W`: f (31), W (rows ≤ 30); `S_w`: f, queries (31), ρ (32); `claim` and `rhs2`: absorbed at 33. No Merkle binding needed. | ≤ 1 (`lambdaBad_card_le_one`) | `a ≈ 2^-124.0` |
| 34+b, round challenge r_b (new, six) | `C_b ≠ g_b(0)+g_b(1)` and `s_b(r_b) = g_b(r_b)` | `g_b`: f, W, w, λ (33), `r_<b` (earlier rounds); `C_b`: claim, rhs2, λ, earlier certificate entries and challenges; `(c0_b, c2_b)`: absorbed at 34+b. No Merkle binding needed. | ≤ 2 (`roundBad_card_le_two`) | `2a ≈ 2^-123.0` |

Sum of the seven new caps: `13a ≈ 2^-120.30`; each `≤ B` (`new_row_cap_le_B`).

That these families are fixed "for every accepting branch" in the sense the
V8 audit asked (section 8, item a) is: for λ and r_b, immediate, because each
bad set is a function of the decoded transcript prefix alone; for ρ, a theorem
that the opened values at the queried positions are determined by the three
roots before ρ except on the charged binding/collision event. R1 has that
theorem for the folded tree and one family (`QueryResidualBridge`, inside the
Bin commitment model); for two families and three trees it is OPEN.

Why the ρ bad set is 21, not 42: outside the roots of the first-fold
polynomial the batched first-fold check rejects; when the first-fold residuals
are all zero, outside the roots of the second-fold polynomial `S_w ≠ rhs2`,
a false claim the combining challenge and rounds carry forward.

## 4. The reduction

**Deterministic reduction (algebra PROVED IN LEAN; source part OPEN).** Let
`π` be accepted by the Aspis one-transaction verifier. Let `r0`, `r1` be the
first- and second-fold residuals of `π`'s openings, W the relation vector, w
the query-weight vector. If ρ is not in the batching bad set, λ not in the
combining bad set and no round challenge in its round's bad set, then

1. `S_W = claim` (R1's `pair == claim`), `S_w = rhs2` (R1's `actual ==
   a.rhs`), all 22 first-fold equalities `F_i = b_i` and all 22 second-fold
   equalities `e_i = G_i` hold;
2. the 57,607-byte R1 proof built from `π` as below is accepted by R1's
   `tx1(…, 10)`, checkpoint, `tx2`, with the same γ, κ, α0, α1, queries and ρ.

Part 1 is `AspisFuture.StageD.stageCD_sound` (lean/StageDSumcheck.lean), a
model theorem. Its hypotheses `hC` and `hfinal` are the model forms of the
batched first-fold check and the final check; its definitions (`fold`,
`foldAll`, `proverPoly`, `qweight`, `rhs2Of`, `secondResidual`) are model
forms of the Rust quantities. That the Rust computes these values is the
source refinement in section 9. The proof: `sumcheck_sound` gives `claim + λ
rhs2 = Σ f_j (W_j + λ w_j)`; `lambda_sound` splits it; `query_identity` turns
`S_w − rhs2` into `Σ ρ^i r1_i`; `all_zero_of_both_evals_zero_outside_bad2`
gives the 44 equalities.

**From one multiproof per tree to R1's two (PROVED ON PAPER).** The R1 proof
is the R1 magic, then `π[8..OFF_NODES]`, then six zero-padded slots. For a
tree and a batch (queries 0..10 or 10..22) with distinct index set `S_β ⊆ S`
(S all 22 indices; `u/4` for the folded tree), let `Occ(X)` be the nodes on
the root paths of X, leaves included, and `Sib(X)` the nodes outside
`Occ(X)` whose sibling is in `Occ(X)`. The single multiproof supplies
`Sib(S)` in canonical order, and its verification assigns to each node of
`Occ(S)` a value equal to the hash of its children's values, ending at the
root (multiproof.rs:343–389). For `p ∈ Sib(S_β)`: if `p ∈ Occ(S)` its value
was computed; otherwise its sibling is in `Occ(S_β) ⊆ Occ(S)`, so `p ∈
Sib(S)` and was supplied. So batch β's nodes are a function of `π`, and
recomputing batch β from its leaves uses only parent relations that already
hold, reaching the same root. R1's slots hold them because the count is a
function of the index set and R1's slot sizes are worst cases: at depth k
with m occupied nodes at most `min(m, available − m)` siblings, which gives
146/172 (C1, C2; 10 or 12 leaves at depth 18) and 128/150 (folded tree: leaves
below 2^16, plus one sibling at each of depths 1 and 2), and by the same count
296/296/254 for the single multiproofs. A slot too small for some index set
would only make a verifier reject. The other R1 checks read only bytes before
`OFF_NODES`, which are equal, through the same `prepare`; the per-query and
relation checks are part 1. `to_summed_format` (fused.rs:869) implements the
reverse direction and is TESTED on six fixtures; this direction has no code.

**What part 2 does not give.** It is a deterministic implication, not a
transfer of probability. The batching event for `r0` is not in R1's bound
(R1's ρ row covers `r1` only; R1 rejects `r0 ≠ 0` outright), and an R1
adversary built from an Aspis adversary would have to compute the R1 slots and
play two phases. The bound has to come from a re-instance of the composition
over the 40-row transcript (findings 1 and 3), not from citing R1's theorem.

## 5. The three evaluators

PROVED IN LEAN as statements about vectors (model theorems):

- `foldAll_zero_eq_sum`: the iterated fold at 0 equals `Σ_j v_j eqw(r, j)`,
  `eqw` the bit-0-first equality weight (what `equality_tables` builds and the
  final-message evaluation contracts with).
- `query_weight_extension`, `sum_eqw_bitProd`: for `w_j = Σ_i c_i Π_{b in
  bits(j)} t_{i,b}`, the extension is `Σ_i c_i Π_b (1 + r_b(t_{i,b} − 1))`, the
  formula of `query_weight_mle` and, factored in pairs, of
  `query_weight_mle_pairs`.
- `sum_eqw_digits3`, `digit_weights`: a vector `h0(d0)·h1(d1)·h2(d2)` over
  base-four digits has extension `Π_d Σ_m digits[d][m]·h_d(m)` with
  `digits[d] = [(1−a)(1−b), a(1−b), (1−a)b, ab]`: rows 1, 2, 3, 5, 6 of
  `Weights::mle_at`, before their E-valued scale.
- `sum_grouped`: the inactive row, constant on groups, has extension
  `Σ_g weight_g Σ_{j in g} eq_j`, as `mle_at` computes it (the tensor form
  behind `future-d-inactive-tensor` reorders the same sum; TESTED only).
- `sum_range_support`: the Libra row is supported on `j < 4`.

PROVED ON PAPER (TESTED by
`stage_d_extensions_equal_the_direct_sums_over_the_explicit_vectors`): the
vector these extend is the vector `Weights::pair` contracts the final message
with. On the S2 two-fold path `pair` computes rows 1, 2, 3, 5, 6 as
`scale_k Σ_j f_j tensor_k[j]` with `tensor_k[j] = Π_{d=2..4} factors[k][d][(j
>> 2(d−2)) & 3]` (the shared-point branch computes the same products for rows
1 and 3 under its equality guard), row 0 as `Σ_j f_j weight(group(j))`, row 4
as `Σ_{j<4} f_j libra[j]`, and returns `Σ_kind κ^kind parts[kind]`. The map
from these Rust functions to the Lean statements is OPEN.

## 6. Entry into the adaptive bound

### 6.1 Starts and B

Finding 1. The theorem needed is stated there.

### 6.2 Classifier and composition

OPEN: a 40-row protocol instance with the second fresh start; the decoder
extended to rows 33–39 and to the second start frame (finding 4); doomed-prefix
definitions for the new rows (after ρ: doomed iff an R1 terminal equality
fails; after λ: iff `C_0 ≠ Σ f_j u_j`; after round b: iff `C_{b+1}` is not the
true partial sum) with D1/D2/D3 proofs consuming `roundBad_card_le_two`,
`lambdaBad_card_le_one` and `bad2_card_le_21`; the restated
`QueryResidualBridge` for the pair. This is the same kind of work as R1's own
33-row classifier.

### 6.3 Collision envelope (1,161)

R1: `595 + 566`, transcript `115 = 1 + 27·3 + 1 + 4·3 + 17 + 3` (QV-STAGE1).
Aspis one-transaction verifier core, from the code:

- transcript: 115 (same `prepare`) + 1 (fresh start) + 7·3 (rows 33–39) = 137;
- leaves: 22·3 = 66 (every key's leaf hashed, fused.rs:775);
- parents, worst case, distinct parents per level summed over 18 levels: C1
  and C2 `1+2+4+8+16 + 13·22 = 317` each, folded tree `1+1+1+2+4+8+16 + 11·22
  = 275`; total 909 (the same formula gives R1's 447 and 527 exactly);
- checkpoint: 0.

Total ≤ 1,112 ≤ 1,161, so the R1 collision term stays an upper bound, on R1's
conditions (complete counted traces, source-prefix coverage, backend
correspondence), which are open for the new code as for the old.

### 6.4 Account term (2,965) and issued calls (2,322)

> **Correction, 2026-11-11 (ONE-TRANSACTION-GAME.md sections 0 and 2.3).** The issued-call figure
> 2,322 is, in the Lean, Q plus two runs of the model verifier at 1,161 each (the original run
> and the annotation compiler's re-run). It does not come from the two transactions, contrary to
> what this section says. The account term's 2,965 splits as 1,921 + 1,040 + 4; only the 4 audit
> reads exist because of the two transactions, and the other two parts have Aspis analogues only
> if the split-B failure event is kept (an owner decision).


Both derive from the two-transaction account run. The one-transaction run
(`stage2_owned` with `future-one-tx`: `validate_asq8`, statement validation,
`verify_summed_format`, `emit_result`, Pool) has not been counted. If it is no
larger, R1's constants remain upper bounds. Missing input; OPEN.

### 6.5 Query-scan and abort terms

Unchanged: same query derivation; the extractor and its relation are R1's
(acceptance gives R1's equalities off the new bad events, section 4).

## 7. The one-transaction entry

Removed obligation: "the stage 1 checkpoint digest implies stage 2's
assumptions" (`checkpoint`, `resume`, `tx2_common`, the `[3,10]`/`[3,11]`
route analysis, the `Runs` clauses about the checkpoint account). Removed, not
transferred.

Replacing obligation (OPEN), at r1_pool_adapter_owned.rs:438–454: every check
the two-transaction path performed across both transactions is performed in
this invocation before `emit_result`. Two-transaction path: transaction 1
validates the statement decoded from the public account and checks the proof
buffer prefix equals the encoded candidate afterstate and the variant byte
(:389–408); transaction 2 rebuilds the statement from the request and the
authenticated accounts and checks it against the checkpoint's public digest.
One-transaction path: the statement is rebuilt from the request, the
authenticated accounts (the lane snapshot, hence the current root, from the
lane account) and the candidate decoded from the proof buffer prefix with a
canonical re-encode check (r1_pool_adapter.rs:792–808), validated, and the
proof verified against its semantic public part. Needed: a source statement
that the statement verified is the statement settled, that every field the
proof does not bind (current root, sequence number) comes from authenticated
accounts or a guard, and that no account read by one path and not the other
changes the statement. The seventh account is snapshotted at the checkpoint
size and not read (harmless; part of the entry contract). The measurement
tags 8–14 are compiled only without `pool-adapter`; in the deployed build
the Pool route returns first (lib.rs:66–76): a reachability statement is
needed, as for R1. The lifecycle validator still checks R1's `PROOF_BYTES`
(r1_pool_adapter.rs:313); it is outside the release surface by the same route
filter.

## 8. Check against the V8 failures

Sources: docs/research/v8-audit-20261005/B_SOUNDNESS_100.md sections 2, 5, 6,
7 and DECISION.md.

**a. Root counts for a family "fixed before the challenge" with no theorem
that it is fixed (B1, B2).** Section 3 lists, for each new or changed row,
what is fixed, by what and before which challenge. Verdict: for the combining
challenge and the six round challenges the families are functions of the
absorbed prefix, so the gap does not arise. For the batching challenge the
family depends on opened values fixed only by Merkle binding to the C1, C2
and folded roots; the theorem saying so for two families and three trees is
OPEN (R1 has it for one family and one tree). Same shape of gap as B1/B2,
smaller in scope, not closed.

**b. The R19 channel fold ("queries test only the combination", extraction
obligation never closed).** In R19 the combination was taken before the
queries, at the level of committed words, so extraction had to recover the
pair from the combination (gap B2). Here the order is the other way round:
the 22 queries are drawn (row 31) after all three roots (init, row 2, row 30);
each query still opens each committed word individually and every opening is
authenticated separately; only the 22 scalar first-fold equalities are
combined, and the combining challenge ρ (row 32) comes after everything they
read. Off the batching bad event all 22 per-query equalities hold
(`all_zero_of_both_evals_zero_outside_bad2`), which is exactly what R1's
extraction consumes; no extraction from a combination is needed. Verdict: not
the R19 situation, provided the binding theorem of item a holds. The
remaining risk is that theorem, not an extraction obligation.

**c. R547/R548 (reconstructed and true round polynomials agree at a
challenge value never charged).** Modelled as coded: `s(X) = c0 + c1 X + c2
X^2` with `c1 = C − c0 − c0 − c2` (`proverPoly`, `proverPoly_eval` is the
coded update). `s(0) = c0`, `s(1) = C − c0` (`proverPoly_at_zero_one`). When
the running claim is already false, `s ≠ g` and every challenge where `s` meets
`g`, 0 and 1 included, is in the charged set
(`roundBad_contains_every_coincidence`), whose size is at most 2
(`roundBad_card_le_two`). `qm31_sample` outputs 0 with mass `a` like any other
element, so r = 0 is charged at the same rate. When the running claim is true,
a wrong `s` can only make a later claim false, which is not a soundness event.
Verdict: no uncharged coincidence; PROVED IN LEAN for the model; the map to
the Rust update is OPEN.

**d. No Fiat-Shamir theorem for the actual transcript; published theorems
cited from memory.** No sumcheck theorem is cited: the round bound, the chain
and the composition are proved here. Rows 33–39 use `Transcript::scalar_k`,
i.e. `qm31_sample` on one 32-byte block, the same sampler as ρ. R1's sampler
lemma `RhoSamplerBound.modulo_bad_mass` is specialised to R1's ρ bad set; the
generic `R0C.ModuloCounting.event_mass_le` with `encoded_mass_le` takes any
finite set and gives `|bad|·(⌊2^256/P^4⌋+1)/2^256`, so it applies to the new
sets of size 1 and 2 after instantiation (not written; easy). The byte/field
correspondence of `qm31_sample` with that encoded reduction is R1's open
obligation. The Fiat-Shamir theorem for the 40-row transcript does not exist
(findings 1, 3). Verdict: OPEN, and stated as such.

**e. Earlier theorems applied to new objects without re-binding.** R1
theorems this argument relies on, with their status for the new object:

| R1 theorem | Exact content used | Applies? |
|---|---|---|
| `R0C.V3.theorem43` | generic: `accepts ∧ extractFails` mass `≤ Qtot·maxErr rb.ε pr.r + κ Qtot` given D1, chain density, D3, chains read, Inj3 | generic; needs a new instance |
| `UnifiedFiatShamir.soundness_bound` | 33-row instance | does not apply (fixed at 33) |
| `DecodedFirstReadUnionBound.decoded_first_read_bound` | `≤ N·ε`, uniform ε | applies with a new decoder; gives `(Q+42)·B` |
| `StartChargePrefix.starts`, `BinHonestQueryBudget.verifier_starts` | `≤ Q+34`, `≤ 34` over `List.range 33` | do not apply; needs re-binding to 40 rows |
| `StartChargeProbability.restricted_union_bound`, `failure_bound` | `(Q+34)·B` and the R1 total | do not apply |
| `QueryResidualBridge` (`rhoBad`, `rhoBad_card`) | folded residual, one family | needs re-binding to the pair |
| `RhoSamplerBound.modulo_bad_mass` | sampler mass for `rhoBad` | ρ: needs the pair's set; new rows: re-instantiate `event_mass_le` |
| `BinCombinedMerkleCollision.kappa`, `.mass` | collision mass for a stated first-read count | applies with count 1,112 ≤ 1,161, on R1's conditions |
| `PerAttemptEnvelope.B`, `thirty_three_B_lt` | numbers | B is a number; the 33/34-start margin does not apply (finding 1) |
| `MatchingSupport`/q22 (`false_claims_query_containment`), the γ/κ/α rows, list decoding, extractor | consume the per-query and relation equalities | apply through part 1 of section 4, once the classifier is re-instanced |
| `TwoFamilyResidualBatch` (this branch) | algebra | model theorem |

**f. Closed lemmas about fixed mathematical objects with no model of the
verifier.** Every Lean theorem on this branch (`TwoFamilyResidualBatch.lean`,
`StageDSumcheck.lean`) is a mathematical model theorem about fixed objects;
none is a source-helper theorem, a refinement, or a composed security theorem,
and the file headers say so. Theorem counts are not used as progress.

**g. Ambiguity of "100 bits".** Only criteria (A) and (B) are used; no figure
is claimed (sections 1 and 0).

Other V8 lessons touched: section 5's "no-close-anchor" and "far-final"
classes are R1's open or closed extraction questions, unchanged by the Aspis
one-transaction verifier, because acceptance gives R1's equalities off the new
bad events; the full-fibre counterexample concerns the code and thresholds,
which are unchanged.

## 9. Obligations

| Obligation | Status |
|---|---|
| Round: ≤ 2 bad r_b; false claims stay false outside it; every coincidence charged, 0 and 1 included | PROVED IN LEAN `roundBad_card_le_two`, `round_doom_persists`, `roundBad_contains_every_coincidence`, `proverPoly_at_zero_one` (model) |
| Six-round chain | PROVED IN LEAN `sumcheck_sound` (model) |
| Combining challenge ≤ 1 bad λ; both claims outside it | PROVED IN LEAN `lambdaBad_card_le_one`, `lambda_sound` (model) |
| Batching challenge ≤ 21 for the pair; all 44 equalities outside it | PROVED IN LEAN `bad2_card_le_21`, `all_zero_of_both_evals_zero_outside_bad2` (model) |
| Composed statement for the batched first-fold check and the final sumcheck | PROVED IN LEAN `stageCD_sound` (model) |
| Evaluator identities about vectors | PROVED IN LEAN (section 5) (model) |
| Arithmetic: 35·B > 2^-100; new caps ≤ B; kind-indexed margin; ceiling bound | PROVED IN LEAN `starts35_exceed`, `new_row_cap_le_B`, `perKind_margin`, `ceil_mass_le` |
| Challenge ledger and absorb order; no unchecked byte | PROVED ON PAPER (section 2) |
| R1 slots from the single multiproofs; slot fit | PROVED ON PAPER (section 4) |
| `pair` contracts f with the W that `mle_at` extends | PROVED ON PAPER (section 5); TESTED |
| Single-multiproof slot sizes 296/296/254 | PROVED ON PAPER; TESTED `merged_slot_bounds_are_attained_by_the_bit_reversed_index_sets` |
| Verifier-core reads ≤ 1,112 | PROVED ON PAPER (section 6.3), given QV-STAGE1's 115 |
| Statement binding over 13 fields; current root unbound by the proof | TESTED `aspis_one_tx_statement_binding` |
| Rust batched first-fold check computes `Σρ^i F_i`, `Σρ^i b_i`, `Σρ^i G_i` | TESTED (`batched_sums_equal_the_pinned_per_query_kernels_on_arbitrary_and_edge_inputs`, `tight_lane_kernels_*`); refinement OPEN |
| Rust final sumcheck refines the Lean model | TESTED (`stage_d_*`); refinement OPEN |
| Single multiproof per tree authenticates the 22 leaves; `digest_into` equals `digest`, including the direct `sol_sha256` call | TESTED (`summed_format_*`); OPEN |
| Exact arithmetic replacements (section 10, class 1), including the canonical-limb precondition of the sixteen-product multiplication at every call site | TESTED; OPEN |
| One-transaction entry statement (section 7) | OPEN |
| Binding of the openings before ρ for two families and three trees (restated `QueryResidualBridge`) | OPEN |
| 40-row protocol instance, decoder, classifier D1–D3 | OPEN |
| Kind-indexed start charge (finding 1) | OPEN; owner decision on use |
| Sampler mass for the new bad sets (instantiate `ModuloCounting.event_mass_le`) | OPEN (routine) |
| One-transaction account-run read count; issued-call count | OPEN (missing input) |
| One-phase game definition | OPEN |
| Knowledge extraction cost, campaign accounting | R1 obligations, unchanged, OPEN there |
| Transcript domain: final sumcheck start; version separation | owner decision (finding 4) |

No trust assumption is added. Missing source refinements are OPEN items, not
assumptions.

## 10. What the Aspis one-transaction verifier invalidates in R1's refinement

From `git diff d7142292c48..8a4059c8bc2 -- crates programs` and the deployed
feature set. Classes: (1) same statement, new local proof; (2) restructured
or new, needs a new refinement proof; (3) obligation removed from this path;
(4) not in the deployed build or not reachable from its entry.

| Function (file) | Feature | Class |
|---|---|---|
| `QM31::mul` sixteen-product form (aspis-core field.rs) | future-fast-kmul | 1; precondition "all limbs canonical" at every call site |
| `PreparedQm31Multiplier::mul` (field.rs) | future-fast-prepared | 1 |
| `QM31::square` (field.rs) | future-fast-square | 1 |
| `QM31::mul_add` (new) and its call in the semantic round polynomial (r1_semantic.rs) | future-lazy-horner | 1 |
| `semantic_boundary` (r1_semantic.rs) | future-lazy-boundary | 1 |
| `ValidatedRecord::decode_k` direct limb load (r1_wire.rs) | future-validated-decode | 1, relies on `Prefix::parse` having checked the same bytes |
| `Digest32::digest_into`, `SolanaDigest::digest_into` (digest.rs, lib.rs) | used by the single multiproofs | 1 |
| `canonical_scan` dispatch (candidate.rs) | future-word-scan off | wrapper 1; word scan 4 |
| `merkle_tail_single_pass`, `merkle_verdict`, `multiproof::verify_counting`, `verify_counting_direct` in `batch_tree` | future-merkle-single-pass, -in-place | 4 for `batch_tree`; `merkle_verdict` is reused by the single multiproofs (2) |
| `prepared_claim` rows; `validate_record_fields_lean`; lean dot pushes; `extension_lanes_tight`; `k_mul_sixteen` | off / probe | 4 |
| `verify_summed_format`, `parse_shape_summed`, format layout | — | 2 |
| `merged_keys`, `merged_tree`, `merged_merkle`, `multiproof::verify_counting_merged`, `node_count_merged`, `well_formed_merged` | — | 2 |
| `fold_sums`, `coefficients`, `base_lanes_tight`, `extension_lane`, `cubic`, the shared-edge second fold, `KbyKDot` | future-tight-base, future-fold-shared | 2 (replace R1's per-query `query_values`, `four_dots`, circle and line folds on this path) |
| `summed_final_checks`, `claims_bytes`, `equality_tables`, `query_weight_mle_pairs` | future-d-pair-expansion | 2 |
| `Weights::mle_at` including the inactive tensor form | future-d-inactive-tensor | 2 |
| `Transcript::new` used for the final sumcheck's fresh start | — | 2 (new use; rows 33–39) |
| one-transaction block of `stage2_owned`, `scan_proof_buffer` length, `stage2` buffer size, `stage1` rejection (adapter) | future-one-tx, -lean | 2 |
| `finish_relation_round`, `relation_view`, `prepare`, `Prepared::new`, `canonical_scan_pinned`, `QueryGeometry::for_range`, `factored_s2_libra_weights` | — | unchanged, still on the path; R1 refinement reusable at the same source where it exists |
| `Weights::pair`, `finish_relation`, `finish_query_dot`, `query_values`, `query_loop`, `accumulate_batched_with_node`, `BatchedWeights`, `batch_merkle`, `batch_tree` | — | 3 (not called; `pair` remains the definition of W) |
| `tx1`, `tx2`, `tx2_common`, `tx2_authenticated`, `checkpoint`, `resume`, `validate_checkpoint_queries`, `read_checkpoint_*`, `stage1_owned`, two-transaction `stage2_owned` body | — | 3 |
| `accumulate_weights(_tight)`, `stage_d_vectors`, `stage_d_rounds`, `final_message_certificate`, `to_summed_format`, `verify`, `verify_batched`, `verify_summed` | — | 4 (prover, test or measurement only) |

## 11. Validation that ran

- `cd /Users/dominic/ZK/AspisFormal && lake env lean -M7000
  /Users/dominic/ZK/.worktrees/future-version/docs/research/future-version/lean/StageDSumcheck.lean`:
  exit 0, 8.9 s wall, peak RSS 1.90 GB, 0 swaps (macOS `time -l`), no
  warnings. All 19 printed theorems depend on exactly `[propext,
  Classical.choice, Quot.sound]`. No `sorry`, `admit`, `axiom`,
  `native_decide` or raised heartbeats. One option: `exponentiation.threshold
  600` on `perKind_margin` only, so `2^454` evaluates (Lean's default is 256).
  Source revision: this commit.
- `TwoFamilyResidualBatch.lean` recompiled unchanged: exit 0, 10.7 s, standard
  axioms (existing result, rechecked).
- `cargo test --offline -p aspis-r1-cost-probe --lib --features
  private-leaf-salts,aspis-core/future-fast-kmul,aspis-core/future-fast-prepared,aspis-core/future-fast-square,aspis-core/future-lazy-horner,future-validated-decode,future-merkle-single-pass,future-tight-base,future-tight-weights,future-lazy-boundary,future-d-inactive-tensor,future-d-pair-expansion,future-merkle-in-place,future-fold-shared
  -- stage_d summed_format merged_slot rho_dependent batched_sums`: 8 passed,
  exit 0 (debug build; tests are small).
- `cargo test --offline --release -p aspis-r1-cost-probe --features prover
  --test aspis_one_tx_statement_binding`: 2 passed, exit 0 (the lead's test,
  rerun to verify, not trusted).
- Not run: package builds, Lean replays beyond these two files, SBF builds,
  host jobs.

## 12. Next deliverable

The kind-indexed version of `decoded_first_read_bound` and the 40-row start
count split by kind (finding 1), after the owner's decision on finding 4,
since removing the final sumcheck's fresh start changes the count the lemma
must cover. Without that theorem the Aspis one-transaction verifier has no
route to criterion (A) through the R1 development.
