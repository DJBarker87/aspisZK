# R1_SOUNDNESS — ledger scaffold (lead, 2026-10-13)

Status: **scaffold**. Rows and caps are fixed here; no row is closed. A row
closes only with a compiled theorem at the R0 standard (`#print axioms` =
`[propext, Classical.choice, Quot.sound]`, host receipts) or an assumption the
user has explicitly accepted in the PLAN. Numbers below are the arithmetic of
`docs/research/100bit-spend-path-20261013/security_ledger.py` (checked), not
theorems. Governing decisions: Rust PLAN "Lead review of the
`codex/100bit-spend-path-20261013` checkpoint (2026-10-13)" (gate G_R1), the
privacy LOG D20 series, and `REUSE-INVENTORY.md` (2026-10-11) in this
directory.

## Protocol under ledger (R1 S2)

R0 semantic phase unchanged: 29 committed lanes (M31/QM31 words), Pair Forest
relation, R0 terminal with the Libra fourth row (D14), mask protocol, 25
semantic challenges in the QM31 subfield `K₄ ⊂ E = WideExact` via `semChal`.
Opening layer: D18 transport `π_R1` (τ = [3,4,2,0,1], σ = id); batching
γ ∈ E over the committed words directly (no chord quotient); κ ∈ E weighted
pairing of six per-lane functionals (three multilinear points, the Libra
functional, two circle evaluations) plus the inactive sum; two 4-to-1 folds
with α₀, α₁ ∈ E on the line domain 2^18 → 2^16, intermediate committed word;
final message 64 E-values; 22 distinct queried fibres; final residual batching
ρ ∈ K₄ (QM31). FS: 33 duplex rows (semantic 0–24, circle 25–26, γ 27, κ 28,
α₀ 29, α₁ 30, ρ 31, queries 32 — **to be confirmed against the Rust
transcript in row Src**). No work or grinding credit anywhere.

## Rows

| Row | Obligation | Cap / bound (arithmetic) | Discharge (existing / needed) | Status |
|---|---|---|---|---|
| S | semantic soundness of the 29-lane relation with masks | 435,200·(1/|K₄| + 1/2^256) ≈ 2^-105.27 | `R0P.combined_fiat_shamirZ` (MaskFiatShamir.lean:123) semantic part; needs the 33-row schedule instance (rows 25–32 re-indexed) | REUSE / RE-INSTANCE |
| γ | joint-list matched response on the literal committed words + six per-lane functional discrepancies | (336,869,026,605,739 + 16,800)·⌈2^256/(|E|−1)⌉/2^256 ≈ 2^-199.7 | cap `R0.ListsResponses.B1_card` (:112) and `width29_bad_response_challenges_card_le`; list `Lambda_card` (:51), `R0P.SemD2.candidates_card` (:58), `MaskD2.etaSomeBad_*` (:85); functional union `R0.BadSetBounds.batch_union_bound` (:16) with 100·6·28; root bound `AspisR1.functional_bad_roots_card_le_16800` (checkpoint, algebraic only) | DESIGN (SECURITY-PATH "direct joint-list binding") |
| κ | weighted pairing over the joint list (degree ≤ 6 in κ) | 600·⌈2^256/|E|⌉/2^256 ≈ 2^-238.8 | `batch_union_bound`; `functional_bad_roots_card_le_600` (algebraic) | DESIGN |
| α₀ | first fold matched response (fold-1 code = R0 final code) + round-0 comparison over the list | (9,396,508,281,246 + 600)·⌈2^256/|E|⌉/2^256 ≈ 2^-204.9 | cap `B6_card` (:128), `Wide.MatchedInstances.exactFinal_bad_response_challenges_card_le` (:35); round comparison per TWO-ROUND-BINDING | REUSE + DESIGN |
| α₁ | second fold matched response by the fourfold repeated lift + round-1 comparison | same as α₀ | SECOND-FOLD-LIFT: lift L, averaging P, quartet identities for `storedFirstLineX18` (R0/PolynomialPair.lean) with `T4`, descent (`AspisR1.RepeatedLift.*`, abstract), wrapper around `exactFinal_bad_response_challenges_card_le`; agreement 2,390 parents ⇒ 9,560 ≥ 9,557 | DESIGN (replaces REUSE-INVENTORY obligation (A); no new decoder instance) |
| q22 | 22 queried fibres on 2^18, agreement threshold 9,557 | (1+δ₀)·C(9557,22)/C(262144,22) ≈ 2^-105.14 | existing envelope (R0 final chain); re-instance for the two-fold support argument: |M| ≥ 9,558 initial fibres ⇒ ≥ 2,390 second-fold parents ⇒ restoration on ≥ 38,232 ≥ 38,230 | RE-INSTANCE |
| ρ | final residual batching in K₄: P(T) = Σ_{i<22} residual_i T^i ≠ 0 has ≤ 21 roots | 21·⌈2^256/|K₄|⌉/2^256 ≈ 2^-119.6 | `AspisR1.subfield_bad_card_le_21` (algebraic); needs commitment binding (openings after ρ, committed values fixed except on the charged binding event) and FS glue | DESIGN |
| FS | Fiat–Shamir composition: Qtot·(max row) + hash/oracle collision term, 33 rows, duplex decoders fixed by the four σ hypotheses (semChal rows 0–24, circle samplers 25–26, σQ rows 27–31 — **ρ's decoder is `qm31Sample`, to be fixed**), q22 chain for the query row | Qtot·2^-105.14 + collision | re-instance of `combined_fiat_shamirZ` with `p.rounds = 33` and the new row decoders | RE-INSTANCE |
| Src | Rust ↔ Lean correspondence of the new opening layer: D18 transport, direct γ-batching of committed words, κ pairing of six functionals, line-domain folds with `LineFold` recovery identities, final 64, ρ row, authenticated two-transaction split (tx1 checkpoint digest ⇒ tx2 assumptions) | — | new; depends on G_R1.3's covering argument | OPEN |

Largest row: q22 (≈ 2^-105.14). Every other row is ≥ 2^-119.6. The intended
statement is the R0 form: for every adversary with Qtot oracle queries,
acceptance of a false statement has probability ≤ Qtot·2^-105.14 + the
collision term; it is not an absolute 2^-100 for unbounded queries.

## Resolved and open structural questions (from REUSE-INVENTORY §10)

- Obligation (A) (new 64 → 2^16 decoder instance): **withdrawn** on the
  checkpoint's repeated-lift route; the α₁ row reuses the fold-1 instance.
  `SecondFoldBudget.lean`'s parameter set is retained as arithmetic only.
- Obligation (B) (fold identities on the line domain): **open**; `LineFold.lean`
  gives the field recovery identities; domain commutation and the depth-two
  node identification are rows α₀/α₁'s first Lean items (L1).
- Obligation (C) (two-fold binding without the quotient): **open**, now the
  joint-list route (rows γ, κ, α₀, α₁); no OOD uniqueness assumption.
- OOD points remain circle points, treated as fixed functionals (no
  list-to-unique collision charged) — accepted as the design; the R0C/R0P
  circle modules re-instance rather than retire.
- Queries remain uniform 22-subsets of the 2^18 fibres — confirmed by the
  checkpoint's verifier; `QueryLaw`/`Q22Law` reuse.
- FS round count: 33 for S2 — **to confirm in Src**.

## Lean jobs (after this ledger; one host job at a time; statements fixed by the lead per job)

L1 line-domain fold identities and repeated-lift encoder lemmas (quartets of
`storedFirstLineX18`, `T4`, L/P, complete-quartet cardinality, descent).
L2 α₁ matched response as a wrapper around `exactFinal_bad_response_challenges_card_le`.
L3 the two round-polynomial comparisons (rows α₀, α₁; 600 each).
L4 direct joint-list binding (rows γ, κ) via `batch_union_bound`.
L5 ρ row: root bound + commitment binding + glue.
L6 FS schedule instance (33 rows) and the Qtot composition.
L7 Src correspondence (after G_R1.3).

## Rules

The lead writes each job's statement after reading the sources it touches;
workers stop on any mismatch (the fixed-statement rule). No row is reported
closed without the axiom audit and host receipts. No security claim is made
in any artifact until G_R1.4 closes.

### L1 completed — repeated-lift encoder lemmas (2026-10-13)

Branch `codex/r1-l1-repeated-lift`, base
`0782fa3a7a0e91092121ddc7dcb612b2beee92b5` (the completed ZF-A commit).
The user explicitly authorized this base after a fresh fetch still placed
`origin/v8-reference` at `4edacd5bd`, without the requested lead ZF-A
acceptance. This job does not supply or infer that acceptance.

The new [lean/R1/RepeatedLift.lean](lean/R1/RepeatedLift.lean) proves the
statements L1.1–L1.6 fixed in `L1-L2-REPEATED-LIFT.md`, including the final
`exactFinalLinear_descent_lift` witness, with no added or weakened premise.
The five definitions and two abbreviations have the prescribed meanings:
64 coefficients and 65,536 parent nodes; lift into coefficient slots divisible
by four; projection onto those slots; natural-polynomial evaluation on
`storedLine16X`; repetition on stored children; and the four-child average.

The bit-shift proof uses `Nat.bitIndices_two_pow_mul` and `Chebyshev.T_mul`.
The existing polynomial-level `naturalCoefficientPolynomial_eq_basisSum`
and symbolic `fibreIndexEquiv 64` reindexing give the lift identity. The
geometry uses `reverseBits_childIndex` and the existing `g_pow_2_31` to
identify each child point's fourth power with its log-16 parent. `X_pow_four`
then gives the embedded `T4` identity and `exactFinalLinear_lift`.

For projection, the two opposite stored pairs follow from
`X_zpow_add_halfTurn`; squaring the quarter-turn gives the opposite `T2`
values. A generic ring identity cancels the three nonconstant low factors.
Applying the existing `naturalCoefficientPolynomial_eval_radix4` at these
nodes proves `exactFinalLinear_project`. Descent counts the image of
`S × Fin 4` under `fibreIndexEquiv`: its size is `4 * S.card`, at least 256.
Constancy and projection place this support in the agreement set, contradicting
`exactFinalEncoder_overlap_cap`'s bound 255 unless the messages are equal.
The witness is the zero coefficient lane. No large coordinate universe is
enumerated.

**Host setup and replay.** Used `dombarker@100.108.41.90`, workspace
`/home/dombarker/project-offloads/aspis-fs-generic-20261006`, Lean v4.32.0
and the existing pinned Mathlib/cache. All 88 checked Wide/R0 modules and
directly used AspisFormal source modules matched the authorized base before
the first attempt and remained unchanged at the end. Before 3410, the new
R1 tree was registered in a new host-root `lakefile.toml` with Wide, R0 and
the path dependency AspisFormal; no root lakefile previously existed. The
final registration selects submodules and explicitly qualifies the external
library target as `AspisFormal/AspisFormal`. Both configuration versions and
hashes are recorded in the evidence. The direct `run2.sh` environment and
the existing `g15-lake-focus` configuration were unchanged.

Attempts 3410–3421 ran `sh run2.sh N R1/RepeatedLift 7000 7` directly, one
module at a time; the launcher took its own lock. Caps stayed at MemoryHigh
5G, MemoryMax 7G, MemorySwapMax 0, TasksMax 128, timeout 900 s, Lean
`-j1 -M7000 -DElab.async=false`. Every launch reported 24 GiB populated plus
7 GiB, below 55 GiB. No package or dependency rebuild was started.

3410 found a missing cached `V5FriReleasedLineGeometry.olean`; it was restored
from an existing successful host build with identical source bytes and the
same toolchain, with the source/object/receipt hashes recorded. 3416 reached
Lean's internal memory limit while checking the concrete quartet calculation
(peak RSS 7,169,228 KiB), and concrete coordinate doubling hit the heartbeat
limit. The replacement isolates `doubledFactor_X_sq`, `doubledFactor_map` and
`quartet_low_sum_generic` before applying them to the stored nodes. No cap
was raised. Other failed attempts were local proof syntax, conditional
rewriting, exponent coercion or finite-set notation repairs; no fixed
statement changed.

Focused stages passed at 3412 (L1.1–L1.2), 3415 (L1.3–L1.4), 3418 (L1.5)
and 3420 (complete L1). Final attempt **3421** checks the exact committed
source after making the specified source imports explicit: **exit 0,
8.61 s wall, peak RSS 6,794,228 KiB, swaps 0**, with no diagnostics or
warnings. Next host attempt: **3422**. No unchanged full regression was
repeated.

All three required `#print axioms` results are exactly
`[propext, Classical.choice, Quot.sound]`: `exactFinalLinear_lift`,
`exactFinalLinear_project`, `exactFinalLinear_descent`. The five additional
printed lift/geometry/witness lemmas have exactly the same axioms. The new
source contains no `sorry`, `axiom` declaration, `native_decide`, `admit`,
`maxRecDepth`, `maxHeartbeats` or `decide`. Its only explicit `Finset.univ`
is over `Fin 4`. [r1/l1/evidence.json](r1/l1/evidence.json), in the T2b-1
format, records every attempt, source identities, metrics, diagnostics,
repairs, axioms and host receipt hashes. Only the new Lean file, this section
and that evidence JSON are committed; no binaries, co-author trailer or push.

L1 alone closes no ledger row. L2's matched-response wrapper, the round
comparisons and all other pending obligations remain open. Verdict unchanged:
v7 stands; R1 is a live candidate under G_R1.

### L2 completed — second-fold matched responses (2026-10-13)

**Scope and base.** On `codex/r1-l2-second-fold-matched`, based on completed
L1 commit `364f53b602584a4b763ea0b5ce7ecb392dd2f368`. The user explicitly
confirmed starting L2 from this commit after L1 passed. The reference head
was still `4edacd5bd` when checked; no lead acceptance is inferred. Added
`lean/R1/SecondFoldMatched.lean`, importing `R1.RepeatedLift`. Both definitions
and L2.1–L2.4 from `L1-L2-REPEATED-LIFT.md` are preserved, including the exact
thresholds 2389 and 9557 and the existing `foldChallengeCap`.

**Proofs.** The lifted support is the union of complete child quartets. A
symbolic reindexing by `fibreIndexEquiv` identifies it with the image of
`S × Fin 4`, proving its size is exactly `4 * S.card`. The pointwise curve
identity and L1's `exactFinalLinear_lift` then transport valid responses;
`2389 < S.card` implies `9557 < 4 * S.card`.

For `matchingDecomposition_descend`, the indicative route in the fixed
document cites a support-size bound not present in the statement. The proof
uses projection instead, preserving the statement without adding a premise:
take the zero coefficient lane of each upper component. L1.5 and L1.4 show
that its lower encoding is the quartet average, so it agrees with the lower
received lane at every supported parent, including on small or empty
supports. Apply the linear zero-lane map to the candidate equality supplied
by `final_matchingDecomposition_iff`; this map is a left inverse of
`liftCoefficients`, yielding the lower candidate curve. L1.6's support bound
is not needed for this route.

Finally, `mem_badStrategy_good_iff`, validity lifting and the contrapositive
of matching descent put the second-fold bad-challenge set inside the existing
final-encoder bad-challenge set. `exactFinal_bad_response_challenges_card_le`
gives the unchanged cap. No decoder instance, list-size premise or certificate
is added.

**Host replay and audit.** Used the pinned workspace
`/home/dombarker/project-offloads/aspis-fs-generic-20261006` on
`dombarker@100.108.41.90`, Lean v4.32.0 and its existing cache. Before attempt
3422, verified all 89 checked Wide/R0, directly used AspisFormal and L1
dependency sources, the compiled L1 object, and the host lakefile's R1
registration with Wide, R0 and AspisFormal dependencies. These remained
unchanged after 3425; no host configuration or dependency repair was needed.

Attempts 3422–3425 ran `sh run2.sh N R1/SecondFoldMatched 7000 7` directly,
one module at a time, with the launcher's own lock. Caps stayed at MemoryHigh
5G, MemoryMax 7G, MemorySwapMax 0, TasksMax 128, timeout 900 s and Lean
`-j1 -M7000 -DElab.async=false`. Reservations were 26 + 7 GiB for 3422 and
24 + 7 GiB thereafter, below 55 GiB. No package build, dependency rebuild or
unchanged full regression was run.

3422 found a missing namespace opening for the existing final message/word
types; 3423 passed L2.1–L2.2. 3424 required replacing a conditional simplifier
in the zero-lane left-inverse proof after its condition had already reduced
to `True`. Final attempt **3425** passed the complete committed source:
**exit 0, 3.27 s wall, peak RSS 6,780,408 KiB, swaps 0**, with no warnings or
diagnostics. No resource failure or cap increase occurred. Next attempt:
**3426**.

All four printed L2 results have exactly
`[propext, Classical.choice, Quot.sound]`, including the required
`secondFold_bad_response_challenges_card_le`. The new source has no `sorry`,
`axiom` declaration, `native_decide`, `admit`, `maxRecDepth`, `maxHeartbeats`
or `decide`. Its explicit `Finset.univ` terms and expanded sums are over
`Fin 4`; no large coordinate universe is enumerated.
[r1/l2/evidence.json](r1/l2/evidence.json), in the T2b-1 format, records all
attempts, source identities, host setup, metrics, diagnostics, repairs,
axioms and receipt hashes. Only the new Lean module, this appended section
and the evidence JSON are committed; no binaries, co-author trailer or push.

L1 and L2 now supply the second-fold matched-response bound. Round comparisons,
the q22 support count, runtime domain commutation and the remaining ledger
obligations stay open; no row is closed here. Verdict unchanged: v7 stands;
R1 is a live candidate under G_R1.

## Lead acceptance of L1 and L2 (2026-10-15)

L1 (`364f53b60`, `R1/RepeatedLift.lean`) and L2 (`80f31c364`,
`R1/SecondFoldMatched.lean`) are accepted as fixed in
`L1-L2-REPEATED-LIFT.md`. Reviewed: statements verbatim (L1.1 via
`Nat.bitIndices_two_pow_mul` and `Polynomial.prod_comp`; L1.3 by exponent
arithmetic; L1.5 by reducing the projection to the lift; L1.6 through the 255
overlap cap with the quartet set built by `fibreIndexEquiv`; L2.4 by subset
into the lifted bad set and `exactFinal_bad_response_challenges_card_le`);
no forbidden tokens; `Finset.univ` only over `Fin 4`. Host receipts verified:
L1 attempts 3410–3421, final 3421 exit 0, SHA `4be70e8f…`, eight axiom audits;
L2 attempts 3422–3425, final 3425 exit 0, SHA `d66eb5f9…`, four audits; all
exactly `[propext, Classical.choice, Quot.sound]`; no cap raised.

**Row α₁ (matched response): closed** at cap `foldChallengeCap =
9,396,508,281,246` on the `2^16` stored line domain, 64-coefficient natural
code, threshold 2389 (lifted 9557), with no new decoder instance. Still open
in row α₁: the round-1 comparison (L3) and the runtime fold/domain
commutation (Src). Next Lean job: L3 (statement to be fixed by the lead;
the checkpoint branch's `TwoRoundComparison.lean`/`ConcreteBinding.lean` are
to be read first for reuse).

## Consolidated status (lead review of the spend-path Lean, 2026-10-15)

The spend-path branch (`codex/100bit-spend-path-20261013` at `a17829a77`,
477 Lean files under `docs/research/100bit-spend-path-20261013/lean/`)
already contains most of the L-programme. Decision: **that tree is the R1
soundness development**; the separate L-programme stops (L1/L2 stand as
duplicates, L3 withdrawn). New R1 Lean jobs are issued only for the gaps
below. The branch's Lean jobs used our host lock (`run2.sh`) and read our
build cache; no concurrency violation found.

### Rows

| Row | Status | Where |
|---|---|---|
| γ joint list + six functionals | deterministic bound **proved**: `gammaBad_card ≤ 336,869,026,622,539` | `ConcreteBinding.lean` |
| κ pairing | **proved**: `kappaBad_card ≤ 600` | `ConcreteBinding.lean` |
| α₀ matched + round | **proved**: `firstBad_card ≤ 9,396,508,281,846` | `ConcreteBinding.lean`, `TwoRoundPairing.lean` |
| α₁ matched + round | **proved**: `secondBad_card ≤ 9,396,508,281,846`; repeated lift in `SecondFoldMatched`/`SecondFoldRestoration` (and independently our L1/L2) | `ConcreteBinding.lean`, `TwoFoldExtraction.lean` |
| deterministic binding | **proved**: `ConcreteBinding.binding` — outside the four bad sets, a large matching set yields a tuple in `Λ(W)` with all claims | `ConcreteBinding.lean`, `MatchingSupport.large_matching_implies_claims` |
| q22 | **proved** deterministically (false claims ⇒ matching set ≤ 9,557 and every query inside it: `false_claims_query_containment`); probability via existing `R0C.V3.Q22.q22_bound` | `MatchingSupport.lean`, `QueryResidualBridge.lean` |
| ρ | **proved**: `rhoBad_card ≤ 21` and the accumulator ⇒ residual-batch bridge | `QueryResidualBridge.lean` |
| FS composition | **proved conditionally**: `UnifiedFiatShamir.soundness_bound` (33 rows, `theorem43` reused) gives `Qtot·maxErr + 3Qtot²/2^256`, given D1/D2/D3, an extractor, a decision and `hQ` | `UnifiedFiatShamir.lean` and the Unified* chain |
| S semantic | R0's masked semantic layer; bridges `MaskedSemantic`, `SemanticPrefix*`; composition into the classifier open | — |
| Src | strict wide parser **proved** (model-level); the rest open | `CandidateWideParser*`, `UnrolledWideParser*` |

### Gaps (ordered)

1. **The concrete round-by-round classifier for the 33-row protocol** and its
   D1/D2/D3 proofs, wiring the deterministic results above (and the semantic
   rows) into the doomed-prefix definitions, as `combined_fiat_shamirZ` did
   for R0. No instance exists yet. This is the core remaining soundness proof.
   `D2TableBoundary` records that a naive witness-availability classifier
   fails D2; the classifier must be the existence/agreement kind used for R0.
2. **Terminal hash calls in the verifier model.** The model's decision is a
   pure Boolean; the Rust verifier hashes leaves, paths and the intermediate
   commitment. The oracle-reading wrapper (`TERMINAL-ORACLE-TRANSPORT`) and
   the causal commitment-recovery chain (`CanonicalMerkleRecovery`,
   `ThreeCommitmentRecovery`, `CausalCommitmentStability`) exist; their
   composition with D3 does not.
3. **Knowledge soundness.** Every extractor in R0 and in this branch is
   `Classical.choose`: the theorem is soundness of membership, not knowledge.
   For a spend this matters: a statement naming another user's note can have
   a witness the attacker does not know. An efficient extractor (list
   decoding by the GRS route in `GS-DECODER-REUSE-PATH.md`, with a running-time
   bound) and a knowledge-soundness statement are required before any
   release claim. This also applies to R0's proved theorem as stated.
4. **Query budget.** `hQ` is a parameter. The claim is the standard per-query
   form (≈ 2^-105.1 per oracle query); no absolute bound for unbounded Q
   exists for any hash-based argument.
5. **Source correspondence** beyond the parser: transcript order, folds,
   checkpoint/account parsing, settlement.
6. **Replay.** Only focused replays were run. One frozen-manifest replay of
   the whole tree under AGENTS.md rules is required before any row is cited
   as closed.

Privacy is tracked separately (privacy LOG; T2b-2b design running).
