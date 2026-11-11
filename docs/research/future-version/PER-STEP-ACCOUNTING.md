# Per-step accounting for the Aspis one-transaction verifier

Status, 2026-11-11. Design section (statements) and piece (a) compiled.
Pieces (b) and (c) and the Aspis start count are stated here and not yet
written in Lean. Nothing here is a bound for Aspis until all four are proved
and composed; no figure is quoted. R1's claim is not restated or tightened.

Owner decision (2026-11-11): for Aspis, a bound proved by charging each
transcript start its own row's cap, with the adversary's starts charged the
largest cap, is acceptable. This note states exactly what that proof is.

Sources: the L187 release closure (read-only copy of its sources); module
names below are L187 names. "R1" is the two-transaction verifier.

## 1. Statements

Notation as in R1: `Dec X M C I A Y` a causal decoder (address and pre-read
table to an optional chain start `(own, pend, g)`), `blaw g obs own pend` the
background law of that start's chain, `hitsChain3 dec bad t log` the event
that some decoded chain in `log` hits its bad set, `lazyMean q t f` the
memoized lazy-oracle mean of program `q` from table `t`.

### (a) Weighted decoded first-read bound — COMPILED

R1 (`DecodedFirstReadUnionBound.decoded_first_read_bound`):

```
(hε : 0 ≤ ε)
(hbad : ∀ a T own pend g, dec a T = some (own,pend,g) →
          blaw g (fun out => indicator (bad out.1 out.2.1 T out.2.2)) own pend ≤ ε)
(hN : DecoderReadsBound dec q t N)
⊢ lazyMean q t (fun v => indicator (hitsChain3 dec bad t v.1)) ≤ N * ε
```

Aspis-side generalisation (`AspisPerStep.WeightedFirstRead.weighted_decoded_first_read_bound`,
lean/AspisWeightedFirstRead.lean):

```
(wt : I → Table I A → ℚ)
(hbad : ∀ a T own pend g, dec a T = some (own,pend,g) →
          blaw g (fun out => indicator (bad out.1 out.2.1 T out.2.2)) own pend ≤ wt a T)
(hW : WeightedReadsBound dec wt q t W)
⊢ lazyMean q t (fun v => indicator (hitsChain3 dec bad t v.1)) ≤ W
```

with the pathwise weighted budget

```
WeightedReadsBound dec wt (.done _) t W           := 0 ≤ W
WeightedReadsBound dec wt (.ask i next) t W       :=
  match t i with
  | some a => WeightedReadsBound dec wt (next a) t W
  | none   => if dec i t = none then ∀ a, WeightedReadsBound dec wt (next a) (put t i a) W
              else ∀ a, WeightedReadsBound dec wt (next a) (put t i a) (W - wt i t)
```

Differences, quantifier by quantifier:

- `ε : ℚ` becomes `wt : I → Table I A → ℚ`. **Kind**: the charge of a start is
  a function of the start's address `i` and of the table `t` before the
  oracle answer at `i` is drawn. Both are fixed before that start's
  challenge: the challenge of the chain begun at `i` is read from the oracle
  at or after `i`, and `t` is the table before `i`. So the budget after a
  start does not depend on the answer (`W − wt i t` is the same for every
  `a`), which is what makes the induction go through.
- `hε : 0 ≤ ε` is dropped. Not needed: the only place R1 used it is a branch
  where `dec i t ≠ none` but no chain start exists, which is impossible; the
  new proof discharges that branch by contradiction. A negative charge is
  harmless for soundness because the hypothesis `hbad` then cannot hold for a
  start with positive bad mass.
- `N : Nat` with `0 < N` at each start becomes `W : ℚ` with `0 ≤ W` at the end.
- Conclusion `N * ε` becomes `W`.

Check against R1: `uniform_weighted_of_count` proves `DecoderReadsBound dec q t
N → WeightedReadsBound dec (fun _ _ => ε) q t (N * ε)` for `0 ≤ ε`, and
`decoded_first_read_bound_via_weighted` derives R1's exact statement (same
hypotheses, same conclusion) from the new theorem. So the premises of (a) are
satisfiable whenever R1's are, and they do not contain the conclusion:
`WeightedReadsBound` is a deterministic condition on the program tree and the
decoder, with no probability and no mention of `bad`.

Why the pathwise form (as proposed): it is the exact shape of R1's induction
(`DecoderReadsBound` with the decrement `N − 1` replaced by `W − wt i t`), so
the proof is R1's with one changed line, and the trace form follows the same
way as R1's. A static "sum of caps over decoded addresses" form would need
the set of addresses fixed in advance, which an adaptive adversary does not
give (the reviewer's point about `mean_firstHit_union_le`).

Trace form, also compiled: `decoderFirstWeight dec wt t tr` (R1:
`decoderFirstReads`, a `Nat`) sums `wt i t` over fresh decoded cells of a
trace, and `weightedReadsBound_of_traces` (R1: `decoderReadsBound_of_traces`)
turns `∀ H, decoderFirstWeight dec wt t (eval (complete t H) p).1 ≤ W` into
`WeightedReadsBound dec wt p t W`. Helpers for (c): `decoderFirstWeight_append`
(R1: `decoderFirstReads_append`), `decoderFirstWeight_le_count_mul` (charges
`≤ w` give weight `≤ count · w`), `decoderFirstWeight_const` (one charge gives
`count · ε`).

### (b) Per-start density for the R1 decoder — STATED

R1 (`RawAdaptiveClassifierHitDensity.adaptive_decoded_classifier_le`):

```
RawAdaptiveLiteralDecoder.decode pubChoice words a T = some (own,pend,g) →
blaw g (fun out => indicator (classifier out.1 out.2.1 T out.2.2)) own pend ≤ PerAttemptEnvelope.B
```

Per-step form (to write, `AspisPerStep.RowCharge.adaptive_decoded_classifier_le_charge`):

```
RawAdaptiveLiteralDecoder.decode pubChoice words a T = some (own,pend,g) →
blaw g (fun out => indicator (classifier out.1 out.2.1 T out.2.2)) own pend ≤ charge pubChoice a T
```

where

```
component pub a : Nat :=            -- the dispatch of UnifiedDecoder.decode, as a function
  if (PublicInitParse.parse pub.pubBytes a).isSome then 0
  else match parseAbsorb a with
       | some (_, label, _) => UnifiedLabels.row label
       | none => 33

classCap n : ℚ :=
  n = 0         ⇒ LiteralClassifier.budget 0
  1 ≤ n ≤ 25    ⇒ max_{1≤i≤25} LiteralClassifier.budget i
  n = 26        ⇒ LiteralClassifier.budget 26
  27 ≤ n ≤ 30   ⇒ max_{27≤i≤30} LiteralClassifier.budget i
  n = 31, 32    ⇒ LiteralClassifier.budget n
  n ≥ 33        ⇒ 0

charge pubChoice a T : ℚ :=
  match pubChoice a T, CanonicalRawTrace.decode L a with
  | some pub, some ac => classCap (component pub ac.val)
  | _, _ => 0
```

**Kind** is `component pub a`: a function of the address bytes and of the
public statement the decoder selects from `(a, T)`. It is fixed before the
start's challenge for the same reason as in (a).

Why classes, not rows, for rows 1–25 and 27–30. `UnifiedDecoder.component`
sends every label 1–25 to the same semantic decoder and every label 27–30 to
the same opening decoder; the row those decoders decode is
`ctx.records.length`, parsed from the table, not the label. No lemma in the
tree says the two agree. So within those two classes the charge is the class
maximum. This is the only place where the per-step form is coarser than "each
start its own row's cap"; its cost is small (section 3) and the smallest
change that would remove it is one lemma per decoder: the parsed
`ctx.records.length` equals `UnifiedLabels.row label` of the address.

Why (b) needs no change to R1 files. `RawUnifiedDecoder.decoded_bound` and
`UnifiedDecoderBound.decoded_bound` take one bound `B` for all 33 rows
(`hfixed : ∀ i < 33, …`), so they cannot give a per-row bound (the reviewer's
point). But the component laws they dispatch to (`UnifiedInitialLaw`,
`UnifiedSemanticLaw`, `UnifiedReseedLaw`, `UnifiedOpeningLaw`,
`UnifiedQueryLaw`, `JointUnifiedBound`, each `.decoded_bound`) take `hfixed`
only for the rows of their own component. The plan is a new dispatcher, a
copy of `UnifiedDecoderBound.component_bound` with `B := classCap n` in each
branch, then copies of the two thin wrappers (`RawUnifiedDecoder.decoded_bound`,
`RawAdaptiveClassifierHitDensity.literal_decoded_classifier_le`) that pass the
class instead of one `B`. Each branch's `hfixed` is discharged as R1 does,
with `LiteralBudgetEnvelope.row_le` replaced by `budget i ≤ classCap n` for
`i` in the class. Risk: if some branch's law needs `hfixed` at a row outside
its class, this fails there; reading the six laws' statements (above) shows
none does.

### (c) Weighted start count for R1's 33 rows — STATED

R1 (`Frozen2StartChargePrefix.starts`, via `BinHonestQueryBudget.verifier_starts ≤ 34`):

```
(hq : ∀ H, (eval H P).1.length ≤ Q)
⊢ decoderFirstReads RecordedBinaryExperimentBin.dec emptyTable (eval H (charged D P)).1 ≤ Q + 34
```

Per-step form (to write, `AspisPerStep.RowStarts.charged_weight`):

```
(hq : ∀ H, (eval H P).1.length ≤ Q)
⊢ decoderFirstWeight RecordedBinaryExperimentBin.dec (charge RawFullPublicSelection.select)
     emptyTable (eval H (charged D P)).1
   ≤ Q * capMax + Σ_{n<33} classCap n + capMax
```

with `capMax = max_n classCap n` (the largest row cap, as the owner decision
allows for adversary starts). Proof plan: the charged log is the prover's log
followed by the 33 sampler rows (`charged_eval`, as in R1). Prover part:
`decoderFirstWeight_le_count_mul` with `capMax`, then R1's
`DecoderQueryAccounting.starts_le_queries` (≤ Q). Verifier part, row by row,
the weighted analogue of `BinHonestQueryBudget.sampler_starts`: a plain row n
reads its absorb frame, the squeeze and the advance; squeeze and advance
never decode (`reject_squeeze`, `reject_advance`, used by R1); the absorb frame
`absorbA p s (label n) data` has `component = n` by
`PublicInitAbsorbSeparation.parse_init_absorb_none` and
`parseAbsorb_absorbA` with `UnifiedLabels.row_label` (the same facts R1's
`UnifiedDecoder.decode_of_absorb` uses), so it costs at most `classCap n`.
Row 0 reads the initial frame (component 0). Row 26 additionally reads the
reseed frame; its component is not determined here, so it is charged
`capMax` (the `+ capMax` term), conservative. Row 31's query chain reads no
decoded address (`query_tail_zero`, R1).

Differences from R1: `Nat` count becomes a `ℚ` weight; `Q + 34` becomes
`Q·capMax + (verifier charges)`; the hypothesis `hq` is unchanged.
Satisfiability: identical premise to R1's.

### Aspis start count (41 rows) — STATED

Aspis transcript: R1 rows 0–32 (with the row-26 reseed), then the combining
challenge (row 33) and six round challenges (rows 34–39), all plain rows
continuing the opening transcript (no new reseed, commit `a63f0dfc35c`).
Starts: 34 + 7 = 41.

```
(hq : ∀ H, (eval H P).1.length ≤ Q)
⊢ decoderFirstWeight decAspis (chargeAspis select) emptyTable (eval H (chargedAspis D P)).1
   ≤ Q * capMaxAspis + Σ_{n<33} classCap n + capMax + capLambda + 6 * capRound
```

`capLambda` and `capRound` are the new rows' caps (sampler mass of a bad set
of size 1 and 2 under `qm31_sample`), `capMaxAspis = max(capMax, capLambda,
capRound) = capMax`.

What extends and what is new for rows 33–39:

| R1 definition | Aspis |
|---|---|
| `UnifiedLabels.label`, `.row` | extend as is: labels `0xa0+n` for n ≤ 39 are distinct bytes (`(160+n) % 256`, n < 96); `row_label` needs `n < 40` instead of `n < 33` (new lemma, same proof) |
| `UnifiedDecoder.component`, `.decode` | new instance: components 33–39 dispatch to a new final-sumcheck decoder; `component_none` moves to `n ≥ 40` |
| context parsers (`UnifiedSemanticContext`, `JointContext`) | new parser for prefixes of 33–39 records: the R1 33-record prefix plus the absorbed `claim ‖ rhs2` and round messages |
| `UnifiedSampler.samp`, `LiteralByteProtocol.protocol`, `rows` | new 40-row instance; rows 33–39 are `plain` samplers with the `qm31_sample` decoder |
| `LiteralClassifier.bad`, `.budget` | new classifier: R1's for rows 0–32 except that the row-32 doomed condition covers the residual pair (first-fold and second-fold); rows 33–39 doomed as in SOUNDNESS-ARGUMENT.md section 6.2 |
| `LiteralClassifier.density` for rows 33–39 | new: from `lambdaBad_card_le_one`, `roundBad_card_le_two` (StageDSumcheck.lean) and `R0C.ModuloCounting.event_mass_le` |
| row-32 density | re-bind: `RhoSamplerBound` is stated for `QueryResidualBridge.rhoBad` (one family); Aspis needs it for `bad2` (two families, ≤ 21) |
| `RawUnifiedDecoder`, `RawLiteralDecoderDensity`, `RawAdaptiveLiteralDecoder`, `RecordedBinaryExperimentBin.dec` | new instances over the new unified decoder (same constructions) |
| pieces (a), trace bridge | reused unchanged (generic) |
| the classifier's D1/D2/D3 and the extractor link for the 40-row protocol | new (the composition obligation of SOUNDNESS-ARGUMENT.md) |

## 2. Validation

| Attempt | Source sha256 | Exit | Wall | Peak RSS (time) | cgroup peak | Axioms |
|---|---|---|---|---|---|---|
| PSA-a-01 | 3a8923e5…720c7ef | 0 | (one unused-variable warning) | — | 395,759,616 B | 7 × `[propext, Classical.choice, Quot.sound]` |
| PSA-a-02 | 6a7d0715…f311a1e | 0 | 3.67 s | 3,578,876 KB | 394,932,224 B | 7 × `[propext, Classical.choice, Quot.sound]`, no warnings |

Command: `bash fv_scope64.sh <attempt> 240 bash fv_lean_one.sh AspisWeightedFirstRead`
on the build host against the L187 objects (scope MemoryHigh 6G, MemoryMax
8G, no swap). PSA-a-02 differs from PSA-a-01 only by removing an unused
hypothesis from `decoderFirstWeight_le_count_mul`. No scratch stand-in file
was used.

## 3. Numeric corollary

Not computed yet: it must follow from (a), (b), (c) and the Aspis instance,
and will be done last by exact rational arithmetic.
