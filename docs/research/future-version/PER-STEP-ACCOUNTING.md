# Per-step accounting for the Aspis one-transaction verifier

Status, 2026-11-11. Pieces (a), (b), (c) for R1's 33-row model are compiled
against the L187 objects, and so is their composition (the weighted form of
R1's restricted union bound). The Aspis 40-row instance is not written; it is
scoped in section 4. Nothing here is a bound for Aspis until that instance is
proved and composed; no figure is quoted. R1's claim is not restated or
tightened (the composed theorem below concerns R1's model only as the
template for Aspis; whether R1 adopts it is a separate decision).

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

### (b) Per-start density for the R1 decoder — COMPILED

R1 (`RawAdaptiveClassifierHitDensity.adaptive_decoded_classifier_le`):

```
RawAdaptiveLiteralDecoder.decode pubChoice words a T = some (own,pend,g) →
blaw g (fun out => indicator (classifier out.1 out.2.1 T out.2.2)) own pend ≤ PerAttemptEnvelope.B
```

Per-step form (`AspisPerStep.RowCharge.adaptive_decoded_classifier_le_charge`, lean/AspisRowCharge.lean):

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

classCap n : ℚ :=                  -- as compiled (AspisRowCharge.classCap)
  n = 0         ⇒ LiteralClassifier.budget 0
  1 ≤ n ≤ 25    ⇒ LiteralClassifier.budget 1        (the largest of rows 1–25; sem_le)
  n = 26        ⇒ LiteralClassifier.budget 26
  27 ≤ n ≤ 30   ⇒ OpeningSamplerBound.openingCap    (the SUM of the four opening budgets; open_le)
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
tree says the two agree. So within those two classes one charge covers every
row of the class.

**The three coarsenings** (the only places where the compiled per-step form
charges more than "each start its own row's cap"; all conservative):

1. rows 1–25 are charged the class maximum, `LiteralClassifier.budget 1`;
2. rows 27–30 are charged the SUM of the four opening budgets,
   `OpeningSamplerBound.openingCap` (about 2^-199.66), not their maximum;
3. the reseed frame read by row 26 is charged the largest cap `capMax`
   (piece (c)), because its decoded row is not determined here.

Their cost is small (section 3). Optional tightening for 1 and 2: one lemma
per decoder saying the parsed `ctx.records.length` equals
`UnifiedLabels.row label` of the address; for 3, a lemma fixing the reseed
frame's component.

Why (b) needs no change to R1 files. `RawUnifiedDecoder.decoded_bound` and
`UnifiedDecoderBound.decoded_bound` take one bound `B` for all 33 rows
(`hfixed : ∀ i < 33, …`), so they cannot give a per-row bound (the reviewer's
point). But the component laws they dispatch to (`UnifiedInitialLaw`,
`UnifiedSemanticLaw`, `UnifiedReseedLaw`, `UnifiedOpeningLaw`,
`UnifiedQueryLaw`, `JointUnifiedBound`, each `.decoded_bound`) take `hfixed`
only for the rows of their own component. Done that way:
`component_bound_class` is a copy of `UnifiedDecoderBound.component_bound`
whose bound hypothesis is required only for rows `i` with `cls i = cls n`;
`decoded_bound_class`, `raw_decoded_bound_class` and
`literal_decoded_classifier_le_class` are copies of the three thin wrappers;
`decode_component` shows the component `UnifiedDecoder.decode` dispatches to
is `rowOf pub a`. Each branch's bound is discharged as R1 does, with
`LiteralBudgetEnvelope.row_le` replaced by `budget_le_classCap`. As compiled,
the cap of the opening class is R1's `OpeningSamplerBound.openingCap` (the
sum of the four opening budgets, about 2^-199) rather than their maximum,
which avoids comparing the four numerically. No R1 file is changed.

Check against R1: `classCap_le_B` (every class cap ≤ `B`) and
`adaptive_decoded_classifier_le_via_charge` re-derive R1's
`adaptive_decoded_classifier_le` (bad mass ≤ `B`) from (b).

### (c) Weighted start count for R1's 33 rows — COMPILED

R1 (`Frozen2StartChargePrefix.starts`, via `BinHonestQueryBudget.verifier_starts ≤ 34`):

```
(hq : ∀ H, (eval H P).1.length ≤ Q)
⊢ decoderFirstReads RecordedBinaryExperimentBin.dec emptyTable (eval H (charged D P)).1 ≤ Q + 34
```

Per-step form (`AspisPerStep.ChargedWeight.charged_weight`, lean/AspisChargedWeight.lean; verifier part `AspisPerStep.RowStarts.verifier_weight`, lean/AspisRowStarts.lean):

```
(hq : ∀ H, (eval H P).1.length ≤ Q)
⊢ decoderFirstWeight RecordedBinaryExperimentBin.dec (charge RawFullPublicSelection.select)
     emptyTable (eval H (charged D P)).1
   ≤ Q * capMax + verifierCharge
verifierCharge = Σ_{n<33} classCap n + capMax          -- verifierCharge_eq
```

with `capMax` the symbolic maximum of the six class caps (the largest row
cap, as the owner decision allows for adversary starts; `classCap_le_capMax`,
`wt_le_capMax`). Proof, as compiled: the charged log is the prover's log
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
Row 0 reads the initial frame, which is component 0 or decodes nowhere
(`wt_init`: its byte 32 is 84, so it is not an absorb frame). Row 26 additionally reads the
reseed frame; its component is not determined here, so it is charged
`capMax` (the `+ capMax` term), conservative. Row 31's query chain reads no
decoded address (`query_tail_zero`, R1).

Differences from R1: `Nat` count becomes a `ℚ` weight; `Q + 34` becomes
`Q·capMax + (verifier charges)`; the hypothesis `hq` is unchanged.
Satisfiability: identical premise to R1's.

### Composition of (a), (b), (c) for R1's model — COMPILED

`AspisPerStep.ChargedHitMass.restricted_union_bound_weighted`
(lean/AspisChargedHitMass.lean):

```
(hq : ∀ H, (eval H P).1.length ≤ Q)
⊢ lazyMean (projected D P) emptyTable (fun run => indicator (prefixHit D P run))
   ≤ Q * capMax + verifierCharge
```

R1's `Frozen2StartChargeProbability.restricted_union_bound` concludes
`≤ (Q+34) · B` with the same hypothesis and the same left side. The proof is
R1's `hit_mass` followed by (a) with the charge of (b) and the trace budget
of (c). This is the template the Aspis instance has to reproduce over the
40-row transcript; it is not an Aspis result.

### Aspis start count (41 starts) — COMPILED

`AspisPerStep.ChargedWeight40.charged_weight40` (lean/AspisChargedWeight40.lean,
PSA-e-12):

```
(hq : ∀ H, (eval H P).1.length ≤ Q)
⊢ decoderFirstWeight AspisRows40.FinalStarts.decFinal charge40 emptyTable
    (eval H (AspisRec40.ChargePrefix.charged D P)).1
   ≤ Q * capMax + verifierCharge40
verifierCharge40 = verifierCharge + capLambda + 6 * capRound   -- verifierCharge40_eq
```

`charge40` charges a frame of rows 33 to 39 the fixed cap of its row
(`capLambda` at 33, `capRound` at 34 to 39) and every other frame R1's
`charge`; `capMax` is R1's (the largest of the six class caps), which bounds
`capLambda` and `capRound` (`finalCap_le_capMax`). The reseed frame (row 26)
is charged `capMax` on top of its class cap. Items 8 to 10 in
ASPIS-INSTANCE-PLAN.md section 5.

### Composition for the Aspis 40-row experiment (item 14) — COMPILED

`AspisPerStep.ChargedHitMass40.restricted_union_bound_weighted40`
(lean/AspisChargedHitMass40.lean, PSA-e-14):

```
theorem restricted_union_bound_weighted40 (decodePair : AspisAcceptance.Codec)
    (D : LiteralByteProtocol.Decoder) (d : Decision) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q) :
    lazyMean (AspisRec40.HitMass.projected D d P) emptyTable
      (fun run => indicator (AspisRec40.HitMass.prefixHit (classifier40 decodePair) D P run)) ≤
      (Q : ℚ) * capMax + verifierCharge40
```

(`Decision` is `OraclePortStoredExperimentC4.Decision`.) Proof: the rows
agent's `AspisRec40.HitMass.hit_mass` (no hypothesis on the decision), then
(a) `weighted_decoded_first_read_bound` with the charge bound
`decFinal_le_charge40` and the trace budget `charged_weight40` through
`weightedReadsBound_of_traces`.

R1's statement, `Frozen2StartChargeProbability.restricted_union_bound`:

```
(hq : ∀ H, (eval H P).1.length ≤ Q)
⊢ lazyMean (projected D P) emptyTable (fun run => indicator (prefixHit D P run))
   ≤ (Q+34) · B
```

Differences, one by one:

1. Experiment. R1: `OraclePortFrozen2Consumer.projected D P`, the
   two-transaction experiment with R1's fixed decision and 33-row verifier.
   Aspis: `AspisRec40.HitMass.projected D d P`, the same construction with
   the 40-row verifier and the decision `d` a parameter; the theorem holds for
   every `d`, in particular the one-transaction decision `dV_aspis`.
2. Decoder and starts. R1: `RawAdaptiveLiteralDecoder.decode select choose`,
   at most `Q + 34` starts. Aspis: `AspisRows40.FinalStarts.decFinal`
   (`decAspis fin`: R1's decoder for rows 0 to 32, the byte decoder of rows
   33 to 39), at most `Q + 41` starts.
3. Classifier. R1: `RawAdaptiveClassifierHitDensity.classifier`. Aspis:
   `classifier40 decodePair` = `AspisAcceptance.bad decodePair`, which is R1's
   classifier below row 32, the residual-pair event at row 32 (in place of
   R1's rho event at that row), the combining-challenge event at 33 and the
   round events at 34 to 39. It is universally quantified over the pair codec
   `decodePair`; which codec the implementation uses is fixed by the
   acceptance link (item 11), not here.
4. Bound. R1: the uniform `(Q+34) · B`, each start charged `B = 15/2^109`.
   Aspis: per-step charges (owner decision, Aspis only), `Q · capMax +
   verifierCharge40`. R1's own figure is not restated or changed; the
   weighted R1 form `Q · capMax + verifierCharge` in this note remains a
   template, not an R1 claim.
5. Hypothesis. Unchanged: `hq`, R1's bound on the adversary's query count.
6. Event. Both bound the classifier-hit event of the recovered charged
   prefix of the run (`prefixHit`); the tail of the full experiment after the
   charged prefix is not in the event in either theorem.

Kind of theorem: a bound on the mass of the classifier's hit event in the
model experiment. It is not a bound on accepting a false statement; that also
needs the clean event (collision and account terms), acceptance-to-checks and
the extractor link for Aspis, all still open. No security figure follows from
it alone.

### Check of the composition against R1 — COMPILED

`AspisPerStep.ChargedHitMassCheck` (lean/AspisChargedHitMassCheck.lean, a new
file; the files the reviewer read are unchanged): `capMax_le_B`,
`verifierCharge_le : verifierCharge ≤ 34 · B` (from `classCap_le_B` over the
33-term list, `List.sum_le_card_nsmul`, and `capMax_le_B`; no budget numeral
evaluated), `weighted_le_uniform : Q · capMax + verifierCharge ≤ (Q+34) · B`,
and `restricted_union_bound_via_weighted`, which re-derives R1's
`Frozen2StartChargeProbability.restricted_union_bound` (same hypotheses,
same conclusion) from the weighted theorem. This checks the generalisation;
it does not tighten or replace R1's theorem.

### Independent review (soundness lead's reviewer, 2026-11-11, commit 01f06debd00, source reading, nothing compiled)

Verdict per file: `AspisWeightedFirstRead`, `AspisRowCharge`,
`AspisRowStarts`, `AspisChargedWeight` faithful; `AspisChargedHitMass`
faithful with a caveat (no lemma stated its domination by R1's `(Q+34) · B`
or re-derived R1's theorem from it; added since as
`AspisChargedHitMassCheck`, above). The reviewer's references:

- `decoded_first_read_bound_via_weighted` (AspisWeightedFirstRead.lean:194–203)
  matches `DecodedFirstReadUnionBound.lean:29–35` token for token;
- `adaptive_decoded_classifier_le_via_charge` (AspisRowCharge.lean:493–500)
  has the hypotheses and conclusion of `RawAdaptiveClassifierHitDensity.lean:55–60`;
- dropping the nonnegativity hypothesis is sound, because `hbad` forces every
  charge actually used to be nonnegative;
- `sem_le` (:65–89), `open_le` (:98–117), `wt_le_capMax`
  (AspisRowStarts.lean:123), `wt_absorb`/`wt_init` (:136–197) are proved upper
  bounds;
- `component_bound_class` is a faithful copy of
  `UnifiedDecoderBound.component_bound` (:26–184), the only change being the
  conjunct `cls i = cls n` in `hfixed` (:211), discharged at the six call
  sites; `decode_component` (:176–198) is new;
- nothing feeds `failure_bound` or `F3T_Numeric.total`, so the R1 headline is
  unchanged;
- not established: the Aspis 40-row instance, the 2,965 account term for one
  transaction, and the 0.1507·2^-100 figure;
- the provenance of the L187 objects was not rechecked by the reviewer.

## 2. Validation

All compiles on the build host against the L187 objects (scope MemoryHigh 6G,
MemoryMax 8G, no swap). PSA-a-* and PSA-b-01/02 through
`fv_scope64.sh … fv_lean_one.sh`; from PSA-b-03 on through the locked wrapper
`fv_lean.sh <attempt> <Module>`. "RSS (time)" is `/usr/bin/time` maximum
resident size, which includes the memory-mapped L187 objects; "cgroup peak"
is the scope's `memory.peak`. Every successful attempt's `#print axioms` lines
are exactly `[propext, Classical.choice, Quot.sound]`; no `sorry`, `admit`,
`axiom`, `native_decide` or raised heartbeats in any file.

| Attempt | Module | Source sha256 | Exit | Wall | RSS (time) | cgroup peak | Note |
|---|---|---|---|---|---|---|---|
| PSA-a-01 | AspisWeightedFirstRead | 3a8923e5…720c7ef | 0 | — | — | 395,759,616 | one unused hypothesis |
| PSA-a-02 | AspisWeightedFirstRead | 6a7d0715…f311a1e | 0 | 3.67 s | 3,578,876 KB | 394,932,224 | 7 axiom lines |
| PSA-b-01 | AspisRowCharge | 779a8243…72cf364 | 1 | 59.35 s | 7,168,432 KB | 4,080,873,472 | kernel "excessive memory" in `budget_le_own` (rewriting through `norm_num`/`decide` on budget literals); omega in `decode_component` |
| PSA-b-02 | AspisRowCharge | 8ad22c16…547f1e8 | — | — | — | — | withdrawn before admission (host full; switch to the locked wrapper) |
| PSA-b-03 | AspisRowCharge | 8ad22c16…547f1e8 | 1 | 9.51 s | 3,566,620 KB | 397,787,136 | one omega goal in `sem_le` |
| PSA-b-04 | AspisRowCharge | 4e96e41d…ef590a2 | 0 | 5.73 s | 3,590,556 KB | 408,031,232 | 8 axiom lines |
| PSA-c-01 | AspisRowStarts | fa51013ee13e10deab144c391e60524340b334b0e0b1e55de580adf8801d436d | 1 | 82.53 s | 7,168,380 KB | 3,515,899,904 | `Byte` ambiguous; kernel "excessive memory" in `verifierCharge_eq` (a `simp` that expanded `List.range 33`) |
| PSA-c-02 | AspisRowStarts | 6e61dfd9e351f6ca9da6f991e84deb84b41982ee0e9fef8d9cffaac2f90d9a43 | 1 | 23.25 s | 4,201,508 KB | 444,694,528 | indicator-sum lemma only |
| PSA-c-03 | AspisRowStarts | 4b8aa6d9…be98c | 1 | 19.64 s | 4,200,348 KB | 444,157,952 | tactic order in the same lemma |
| PSA-c-04 | AspisRowStarts | 90ec1d2851a1971ec206ea6944d378d756ad629e3ff7b979356128afc127530f | 0 | 21.62 s | 4,204,012 KB | 426,045,440 | 6 axiom lines |
| PSA-c-05 | AspisChargedWeight | 7fedf4f1…5f5dfd | 1 | 3.07 s | 4,202,980 KB | 417,923,072 | unresolved placeholders in a `have` |
| PSA-c-06 | AspisChargedWeight | cbaad801…db3c37 | 0 | 2.98 s | 4,226,960 KB | 434,352,128 | 1 axiom line |
| PSA-c-07 | AspisChargedHitMass | 17848dff…c31c7d | 0 | 2.00 s | 4,221,664 KB | 429,301,760 | 1 axiom line |
| PSA-c-08 | AspisChargedHitMassCheck | 7afab2bb…69d7 | 0 | 2.42 s | 4,230,180 KB | 428,130,304 | 4 axiom lines |
| PSA-e-12 | AspisChargedWeight40 | 934045c899af9bcf4d369fd90aa94820b2ed208ba333aa514443bf7751f1e404 | 0 | 3.63 s | 4,215,396 KB | 431,779,840 | 1 axiom line (items 8 to 10: ASPIS-INSTANCE-PLAN.md section 5) |
| PSA-e-13 | AspisChargedHitMass40 | 20f7ae0c…c0f5 | 1 | 1.94 s | 4,193,592 KB | 421,072,896 | `Decision` ambiguous (two namespaces opened) |
| PSA-e-14 | AspisChargedHitMass40 | 7b9954b4…4787 | 0 | 2.26 s | 4,213,072 KB | 429,793,280 | 1 axiom line |

The two kernel memory failures were not retried unchanged (AGENTS.md
resource rule 5): in both the proof was asking the kernel to reduce terms
built from the budget definitions or a 33-element list. The replacements
state the needed facts symbolically (`classCap_of_*` by rewriting with small
`Nat` equalities; `sum_indicator26` by induction on the list length) and
compile in seconds. No scratch stand-in file was used.

## 3. Numeric corollary

### 3.1 Start term at Q = 0 (arithmetic from the compiled forms only)

This section follows only from `restricted_union_bound_weighted40` and the
compiled definitions of `capMax` and `verifierCharge40`; it replaces the
earlier estimate made from the stated forms (which agreed). It is not a
security figure: the other terms of the Aspis bound and their transport are
open (below).

Exact rational arithmetic (Python `fractions`) from the L187 definitions:
`LiteralClassifier.budget` (R1LiteralClassifier.lean:40), `SemanticBudget.roots`
and `atom = (1 + deltaQ)/P^4` with `deltaQ = P^4/256^32` (R0P/SemD2.lean),
`LiteralCircleDensity.budget = atom`, `OpeningSamplerBound.openingCap`
(with `gammaAtom`, `atom`), `UnifiedQueryDensity.queryCap =
C(9557,22)/C(262144,22)`, `RhoSamplerBound.rhoCap = 21·perElem`, and
`perElem = (⌊2^256/P^4⌋+1)/2^256`, `capLambda = perElem`,
`capRound = 2·perElem` (AspisRowDensityQM31). `P = 2^31 − 1`, `B = 15/2^109`.

- `capMax = queryCap = C(9557,22)/C(262144,22)`
  = 332233934228956685743727459727502257791407791653047 /
  14872013861920722188613414594812101323350365360984194543156711866198653246277652480
  ≈ 2^-105.1421 = 0.966613 B = 0.028319·2^-100.
- `verifierCharge40 = 1,577,601·atom + 4·openingCap + 2·queryCap + 34·perElem`
  (row 0: 217,600·atom; rows 1–25: 25·54,400·atom; row 26: atom + capMax;
  rows 27–30: 4·openingCap; row 31: queryCap; row 32: 21·perElem; row 33:
  perElem; rows 34–39: 12·perElem). As a reduced fraction (163-digit
  numerator) it is ≈ 2^-102.7305 = 5.142932 B = 0.150672·2^-100.
  The R1 part `verifierCharge` is 5.142905 B; rows 33 to 39 add 13·perElem
  ≈ 2^-120.3.
- **Aspis start term at Q = 0** = `verifierCharge40` = 0.150672·2^-100
  (< 2^-100 as rationals). For comparison only, R1's uniform start term at
  Q = 0 is 34·B = 0.996094·2^-100.
- Q-dependence of the start term alone: `Q·capMax + verifierCharge40 ≤
  (Q+1)·2^-100` for every Q (both `capMax` and `verifierCharge40` are below
  2^-100). This is arithmetic on one term, not the `(Q+1)·2^-100`
  corollary, which needs every term of the total.

`verifierCharge40` as a reduced fraction (checked equal to the closed form
`1,577,601·atom + 4·openingCap + 2·queryCap + 34·perElem`):

```
1062773442900527284618072538139609068208588569703933048511394823620742700175052894973176713647326115520853987471734180279854157888412515638946586489477873528997799
/ 8941454792004069557412375958262374959375728139616530084353653333888736915387129967121165815713683701297109050248842091403735849056796700788700151959357866091657515457228046590292036266575790080
```

Terms carried over unchanged from R1, and their status for Aspis:

- collision `6(Q+1161)^2/2^256`: an upper bound if the Aspis verifier core
  reads at most 1,161 distinct addresses (counted 1,112 on paper,
  SOUNDNESS-ARGUMENT.md section 6.3, on R1's conditions);
- account `6(Q+2965)^2/2^256`: **not justified for Aspis**. 2,965 comes from
  the two-transaction account run; the one-transaction count is a missing
  input. (At Q = 0 it is about 2^-229 and does not affect the comparison.)
- abort `2^-126`, query-scan `2^-454`: same extractor and same query
  derivation as R1; carried over, their transport to Aspis is part of the
  open composition.

The Q-dependent range of the `(Q+1)·2^-100` corollary is computed last, once
(a), (b), (c) and the Aspis instance are proved.

## 4. Scope of the Aspis 40-row instance (estimate, for the owner)

What (a), (b), (c) give is R1's 33-row model with per-step charges. The Aspis
bound needs the same chain for the 40-row transcript. Estimate by component,
from the L187 sources (file counts are new Aspis files, each one module):

| Item | R1 counterpart | Copy or new | Files |
|---|---|---|---|
| labels to n < 40 | `R1UnifiedLabels` | copy, one bound changed | 1 |
| 40-row sampler and protocol | `R1UnifiedSampler`, `R1LiteralByteSampler`, `R1LiteralByteProtocol`, `LiteralTranscript` | copy; rows 33–39 are `DuplexSamplers.plain` with the `qm31_sample` decoder | 3–4 |
| decoder components 33–39 and context parser | `R1UnifiedDecoder`, `R1JointContext`, `R1JointUnifiedDecoder`, `UnifiedDecoderCanonical`, `RawUnifiedDecoder` | the dispatcher is a copy; the parser for prefixes of 33–39 records is new but follows `JointContext` (a list of absorbed records after the query record) | 4–5 |
| laws for the new components | `R1UnifiedSemanticLaw`, `R1JointUnifiedBound` | follows `JointUnifiedBound` | 1–2 |
| classifier events and densities rows 33–39 | `R1LiteralClassifier`, `R1LiteralRhoDensity` | new events (combining challenge, six rounds) built on `lambdaBad_card_le_one` and `roundBad_card_le_two` (StageDSumcheck.lean) and `R0C.ModuloCounting.event_mass_le` | 2–3 |
| row-32 event for the residual pair | `R1LiteralRhoDensity`, `R1LiteralRhoBinding`, `QueryResidualBridge`, `RhoSamplerBound` | genuinely new: the pair's bad set (`bad2`) needs the first-fold residual as a vector of E values read from the committed words, with `match0 ↔ residual = 0` | 2–3 |
| pieces (b) and (c) for 40 rows | this note's (b), (c) | copy with the new components | 2 |
| acceptance to extraction | `R1LiteralAcceptanceTerminal` (`Checks`, `checks_noHit_relation`, `conditional_d3`) | genuinely new: an Aspis `Checks` (batched first-fold equation, `claim`/`rhs2`, certificate rounds in place of `firstMatch` and `pairingChecks`) and a lemma "Aspis checks and no hit at rows 32–39 imply R1's `Checks`", after which R1's `checks_noHit_relation` applies; algebra from `stageCD_sound` | 2–3 |
| the charged/recorded experiment, start-charge prefix, clean event, probability | `Frozen2StartCharge*`, `RawCut*`, `OraclePort*`, `RawRecordedOracleExtractionMassBin` (a family of about 260 files in L187) | mostly re-instantiation over the new protocol and decoder; how much is generic in the protocol was not measured | unknown; at least 5–10 |
| source refinement of the Aspis verifier to the 40-row model | R1's Src obligations | new | not estimated here |

Total, excluding source refinement and the charged-experiment family: about
18–25 new files, roughly two thirds copies with changed row bounds or
dispatch and one third new mathematics.

**Hardest single item:** the acceptance-to-extraction link, i.e. proving that
an accepted Aspis transcript with no hit at rows 32–39 satisfies R1's
`Checks`, in particular `firstMatch : ∀ j, MatchingSupport.match0 data
(queries j)` from the batched first-fold equation. It needs the first-fold
residuals expressed as values fixed by the committed words before ρ (the
two-family, three-tree binding that SOUNDNESS-ARGUMENT.md lists as open), and
it is the place where the R19-type failure would reappear if the order of
data and challenge were wrong.
