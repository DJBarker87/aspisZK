# L3 — the two round-polynomial comparisons: fixed statements (lead, 2026-10-15)

Rows α₀ and α₁ (round parts) of `R1_SOUNDNESS.md`. **Decision: adopt the
spend-path branch's statements** (`codex/100bit-spend-path-20261013` at
`a17829a77`, `docs/research/100bit-spend-path-20261013/lean/`), which the lead
has read and which implement `TWO-ROUND-BINDING.md` exactly. They are
deterministic algebra: no extraction, causality, sampler or FS premise.

## Modules to port into `docs/research/v8-r1-20261011/lean/R1/` (namespace `AspisR1`)

From the branch, in dependency order, statements **verbatim**:

1. `FunctionalBatch.lean` — `functionalBadRoots`, `functional_bad_roots_card_le`,
   `eval_zero_outside_functional_bad_roots`, `functional_bad_roots_card_le_600`,
   `functional_bad_roots_card_le_16800` (imports Mathlib only).
2. `NaturalProjection.lean` — only what `RoundPairing` needs (`childIndex`,
   `parentIndex`, `slotIndex`, `fibreIndexEquiv` and their lemmas); it imports
   `AspisFormal.V5FriNaturalBasisRadix4`.
3. `RoundPairing.lean` — `quarter`, `dot`, `primalFold`, `dualFold`
   (`sourcePerm = [0,3,2,1]`), `roundPolynomial`, `round_degree` (≤ 6),
   `round_eval`, `round_boundary` (`coeff 0 + coeff 4 = quarter · dot`), the Horner lemmas.
4. `TwoRoundComparison.lean` — `comparisonBad`, `comparison_bad_card_le_600`,
   `comparison_eq_of_eval_eq`, `boundary`, `two_round_comparison`,
   `claim_eq_of_compared_boundary`.
5. `TwoRoundPairing.lean` — `round0Truth`, `round1Truth`,
   `round0_bad_card_le_600`, `round1_bad_card_le_600`, `two_round_pairing`.

Plus one corollary, new, in `TwoRoundPairing.lean`:

```
theorem two_round_pairing_r1 (h4 : (4 : K) ≠ 0) … :   -- two_round_pairing at n = 64
  (q : T → Fin 1024 → K) (w : Fin 1024 → K) …
```

i.e. `two_round_pairing` instantiated at `n = 64` (`4·(4·64) = 1024`
coefficients → 256 → 64 final values), stated with `Fin 1024` by a cast lemma
on the index type; no new hypothesis.

## Conditions

- **Duplicate definitions.** `R1/RepeatedLift.lean` (L1) already uses
  AspisFormal's `childIndex` (`V5ComponentCConcreteFoldLinearity.lean:207`,
  `⟨4 i + s, _⟩`) and a `fibreIndexEquiv`. Do not introduce a second
  incompatible copy: reuse the existing definitions where they are the same
  term, or prove a one-line equality lemma; if two genuinely different
  definitions with the same name are needed, STOP and report.
- **What L3 does not deliver** (stays open in the ledger): the candidate
  family `ts` is the joint list `Λ(W)` with `card ≤ 100` (L4 instantiates it);
  `hextract` comes from the fold extraction (L1/L2 and the first-fold
  theorem); the order constraint (the α₀ family fixed before α₀, the α₁
  family before α₁) and the 600-root bounds becoming probabilities belong to
  the FS row (L6); `roundPolynomial`/`sourcePerm`/`quarter` matching the Rust
  verifier is row Src (L7).
- Hard rules, host protocol, evidence format as L1/L2; attempts from 3426;
  `#print axioms` for `round0_bad_card_le_600`, `round1_bad_card_le_600`,
  `two_round_pairing`, `two_round_pairing_r1`: exactly
  `[propext, Classical.choice, Quot.sound]`.
