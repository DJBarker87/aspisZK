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
