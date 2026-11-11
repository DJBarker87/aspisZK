# Row densities for the Aspis one-transaction verifier: rows 32 (pair), 33, 34 to 39

Status, 2026-11-11. Statements below are COMPILED (attempts PSB-02 to PSB-06,
section 5) as theorems in R1's sampler setting. None of them is a bound for
Aspis; no figure is quoted. They supply the per-row inputs that piece (b) of
PER-STEP-ACCOUNTING.md needs ("bad mass of a start of this row ≤ cap of this
row") for the three challenge kinds that are new or changed in Aspis, with the
bad set left abstract. What connects them to the Aspis transcript is listed in
section 6 and is OPEN.

Sources: L187 module names. Lean files (masters):
`lean/AspisRowDensityGeneric.lean`, `lean/AspisRowDensityQM31.lean`,
`lean/AspisRowDensitySampler.lean`, `lean/AspisRowDensityCaps.lean`.

## 1. The sampler and the per-element mass

All three kinds draw a K-valued challenge (K = QM31, `|K| = P^4`, `P = 2^31−1`)
with `qm31_sample` on one 32-byte block. R1's model of it, on a fresh block
`s : State`, is

```
R0P.SemSource.qm31Sample s = qm31Rank (R0C.ModuloCounting.reduce _ (blockRank s))
```

and on every row index `n ≥ 32` R1's selected challenge map has this as its
K-part: `rhoOf (SelectedChallengeMap.sigma n s) = qm31Sample s`
(`QM31.sigma_rho_of_ge`; R1 proves the case n = 32 as `SelectedChallengeMap.rho_row`).

Per-element mass: `perElem = (⌊2^256/P^4⌋ + 1)/2^256`, the factor in R1's
`RhoSamplerBound.rhoCap`. Since `P^4` is odd, `2^256 mod P^4 ≠ 0` and this equals
`⌈2^256/|K|⌉/2^256` (checked numerically; the Lean definitions use R1's
`⌊·⌋ + 1` form and nothing depends on the ceiling form).

## 2. Statements, with the R1 statement each mirrors

### 2.1 Generic set lemma (task item 2)

R1 has the general pieces but composes them only for its row-32 set.
`R0C.ModuloCounting.event_mass_le` (any `f`, any `bad : Finset E`, given a
per-element bound `c`: `mean (indicator (f a ∈ bad)) ≤ bad.card * c`) and
`encoded_mass_le` (per element `(B/n+1)/B`) are general; R1 joins them only in

```
-- R1: AspisR1.RhoSamplerBound.modulo_bad_mass
mean (fun a : A => indicator
  (output (reduce hn (input a)) ∈ QueryResidualBridge.rhoBad iota d q)) ≤
  21 * (((B / n + 1 : Nat) : ℚ) / B)
```

New (`AspisRowDensity.Generic.modulo_set_mass`, `modulo_set_mass_le`):

```
(S : Finset K)                                   -- any finite set
mean (fun a : A => indicator (output (reduce hn (input a)) ∈ S)) ≤
  S.card * (((B / n + 1 : Nat) : ℚ) / B)
-- with (hS : S.card ≤ k): ≤ k * (((B / n + 1 : Nat) : ℚ) / B)
```

Differences: `rhoBad iota d q` becomes an arbitrary `S`; `21` becomes `S.card`
(or `k` with `hS`); the typeclass context shrinks to `[Fintype A] [Fintype K]`
(no field structure, no `E`, `iota`, `d`, `q`). Check against R1:
`QM31.modulo_bad_mass_recovered` has R1's statement verbatim (same binders,
same conclusion) and is proved from `modulo_set_mass_le` and R1's
`QueryResidualBridge.rhoBad_card`.

Specialised to the block sampler (`QM31.qm31_set_mass`, `qm31_set_mass_le`):

```
mean (fun s : State => indicator (qm31Sample s ∈ S)) ≤ S.card * perElem
```

R1 also has `R0P.SemSource.semChal_event` for any `Finset WideExact` with the
looser per-element constant `(1+deltaQ)/P^4 = 1/P^4 + 2^-256`; `perElem` is at
most that (`QM31.perElem_le_slack`).

### 2.2 Row form, state level (shape of R1's `rho_mean`)

R1:

```
-- AspisR1.LiteralRhoDensity
def bad (P : LiteralTranscript.Prefix) (v : WideExact) : Prop :=
  match read P with
  | none => False
  | some (d, q) => rhoOf v ∈ QueryResidualBridge.rhoBad LiteralOpeningView.eK d q
theorem rho_mean (P : LiteralTranscript.Prefix) :
  mean (fun s : State => indicator (bad P (SelectedChallengeMap.sigma 32 s))) ≤ rhoCap
```

New (`AspisRowDensity.QM31`):

```
def setBad (read : C → Option X) (S : X → Finset K) (c : C) (v : E) : Prop :=
  match read c with
  | none => False
  | some x => rhoOf v ∈ S x

theorem row_mean (read : C → Option X) (S : X → Finset K) (k : Nat)
    (hS : ∀ x, (S x).card ≤ k) (n : Nat) (hn : 32 ≤ n) (c : C) :
  mean (fun s : State => indicator (setBad read S c (sigma n s))) ≤ k * perElem
```

and the three instances, each with the bad set abstract and only a cardinality
hypothesis:

| Theorem | Hypothesis | Conclusion |
|---|---|---|
| `combining_mean read S hS n hn c` | `∀ x, (S x).card ≤ 1` | `≤ capLambda` |
| `round_mean read S hS n hn c` | `∀ x, (S x).card ≤ 2` | `≤ capRound` |
| `pair_mean read S hS n hn c` | `∀ x, (S x).card ≤ 21` | `≤ capPair` |

Differences from R1's `rho_mean`: the context `P : LiteralTranscript.Prefix`
becomes any `c : C`; R1's reader becomes any `read : C → Option X`;
`rhoBad eK d q` becomes any family `S x` with `|S x| ≤ k`; row `32` becomes any
row `n ≥ 32`; `rhoCap` becomes `k * perElem`. Check against R1:
`Sampler.rho_bad_eq` proves R1's `LiteralRhoDensity.bad P` is
`setBad LiteralRhoDensity.read (fun dq => rhoBad eK dq.1 dq.2) P`, and
`Sampler.rho_mean_recovered` re-derives R1's `rho_mean` statement verbatim
from `pair_mean`.

Model-connected versions (bad sets from `AspisFinalSumcheckModel`, namespace
`AspisFuture.StageD`, cardinality discharged by the model):

| Theorem | Read type `X` | Set | Card from |
|---|---|---|---|
| `combining_mean_model` | `E × E` = `(S_W − claim, S_w − rhs2)` | `lambdaSet x = lambdaBad eK x.1 x.2` | `lambdaBad_card_le_one` |
| `round_mean_model` | `RoundData = {g : E[X] // g.natDegree ≤ 2} × E × E × E` = `(g_b, C_b, c0_b, c2_b)` | `roundSet x = roundBad eK g cl c0 c2` | `roundBad_card_le_two` |
| `pair_mean_model` | `(Fin 22 → E) × (Fin 22 → E)` = `(r0, r1)` | `pairSet x = bad2 eK r0 r1` | `bad2_card_le_21` |

The degree bound on `g` is part of the read type; for the true round polynomial
the model supplies it (`roundPoly_natDegree_le`).

### 2.3 Row form, sampler level (the classifier's `density` field)

R1's classifier field is
`independentMean (LiteralTranscript.samp P.round P m).toProgram (fun v => indicator (bad P m v.2)) ≤ budget P.round`;
row 32 is

```
-- R1: AspisR1.LiteralRhoDensity.row32_density
(hround : P.round = 32) :
independentMean (LiteralTranscript.samp P.round P m).toProgram
  (fun v => indicator (LiteralOrdinaryDensity.event P m (bad P) v.2)) ≤ rhoCap
```

Row 32, residual pair (`Sampler.pair_row32_density`):

```
(read : LiteralTranscript.Prefix → Option X) (S : X → Finset K)
(hS : ∀ x, (S x).card ≤ 21) (hround : P.round = 32) :
independentMean (LiteralTranscript.samp P.round P m).toProgram
  (fun v => indicator (LiteralOrdinaryDensity.event P m (setBad read S P) v.2)) ≤ capPair
```

Difference: R1's reader and `rhoBad` become abstract; otherwise identical
(same transcript, same event wrapper, same row). Check:
`Sampler.row32_density_recovered` re-derives R1's `row32_density` verbatim.

Rows 33 to 39. R1's literal transcript cannot host them:
`LiteralTranscript.valid` admits payload rows only for `i < 33`, so at row 33
R1's event is `False`. R1's `UnifiedSampler.samp`, which `LiteralTranscript.samp`
calls, is defined for every row index (rows other than 0, 26, 31 are
`DuplexSamplers.plain`), and `UnifiedSampler.unified_law` holds for every
`i ≠ 31` with `messageValid i m` (a constructor check, no row bound). New
(`Sampler.unified_row_density`):

```
(p : FS2.Duplex.Params M E L) (hD : 5 ≤ p.D) (i : Nat)
(P : UnifiedSampler.Prefix M E L) (m : TranscriptView.Message M)
(hi31 : i ≠ 31) (hm : UnifiedSampler.messageValid i m)
(hσ : ∀ s, rhoOf (p.σ i s) = qm31Sample s)
(T : Finset K) (k : Nat) (hT : T.card ≤ k) :
independentMean (UnifiedSampler.samp p hD i P m).toProgram
  (fun w => indicator (ordEvent (fun v => rhoOf v ∈ T) w.2)) ≤ k * perElem
```

with `ordEvent bad ch` = `bad v` on an ordinary value `v`, `False` on a query
value (R1's `LiteralOrdinaryDensity.event` without its `valid` conjunct;
validity is the hypothesis `hm` instead). Read versions
`unified_read_density` (`read : Prefix × Message → Option X`, `|S x| ≤ k`) and
the instances `combining_unified_density` (≤ 1, `capLambda`),
`round_unified_density` (≤ 2, `capRound`), `pair_unified_density` (≤ 21,
`capPair`). `hσ` holds for R1's map on every `i ≥ 32`
(`Sampler.selected_sigma_rho`, for `SelectedTranscriptParams.params`).

Differences from R1 (`LiteralOrdinaryDensity.density` + `rho_mean`): the
parameters `p` are arbitrary (R1: `SelectedTranscriptParams.params`), with the
row's challenge law as hypothesis `hσ`; the row is any `i ≠ 31`; the bad set
may read this row's own message `m` (needed: the combining challenge's set
reads `claim ‖ rhs2`, row 33's payload; a round's set reads `c0_b ‖ c2_b`).

## 3. What each bad set is a function of, and why it is fixed before the challenge

Formally: in every statement above the bad set is a function of objects
quantified outside the mean (`c`, or `P` and `m`), never of the fresh block
`s` (resp. `b`). The sampler-level statements tie this to the transcript
order through R1's `UnifiedSampler.unified_law`: for fixed `(P, m)` the row's
sampler absorbs `m` into the state after `P` and squeezes; its independent
answer law is the mean over one fresh block `b` of `p.σ i b`, and `(P, m)` is
fixed before `b` is drawn. So "fixed before the challenge" holds for anything
the caller computes from `(P, m)`, by the type of the read.

What the caller must compute from `(P, m)` (SOUNDNESS-ARGUMENT.md section 3):

| Row | Set | Inputs | In `P` or `m` |
|---|---|---|---|
| 33, combining challenge | `lambdaBad eK (S_W − claim) (S_w − rhs2)` | f (row 31 payload), W (challenges ≤ 30), queries (row 31 challenge), ρ (row 32 challenge); `claim`, `rhs2` (row 33 payload) | `P` and `m`; no Merkle binding |
| 34+b, round challenge | `roundBad eK g_b C_b c0_b c2_b` | `g_b` from f, W, w, λ (row 33), `r_<b`; `C_b` from claim, rhs2, λ, earlier rounds; `c0_b`, `c2_b` (row 34+b payload) | `P` and `m`; no Merkle binding |
| 32, residual pair | `bad2 eK r0 r1` | `r0` from C1, C2 and folded openings at the queries, γ, α0; `r1` from the final message, query nodes, α1, folded openings | `P` only if the prefix carries the committed words (R1's literal transcript does: C1 word at row 0, C2 word at row 2, folded word at row 30, read by `LiteralMatchingData.beforeRho`); the openings equal the words' values only off the charged Merkle binding/collision event |

For row 32 the read is R1's kind of read of literal words, and the gap named
in SOUNDNESS-ARGUMENT.md section 8a (binding of two families and three trees
before ρ) is not closed by anything here.

## 4. Caps (exact rationals)

`⌊2^256/P^4⌋ = 5444517880876220229045745149051146347264`. Let
`N = 5444517880876220229045745149051146347265`.

| Cap | Definition | Exact value (Lean) | Bound (Lean) |
|---|---|---|---|
| `perElem` | `(⌊2^256/P^4⌋+1)/2^256` | `N/2^256` (`perElem_eq`) | `2^-124 < perElem` (`two_neg_124_lt_perElem`); `≤ 1/P^4 + 2^-256` (`perElem_le_slack`) |
| `capLambda` | `1 * perElem` | `N/2^256` (`capLambda_eq`) | `< 2^-123` (`capLambda_lt`); ≈ 2^-124.000 |
| `capRound` | `2 * perElem` | `2N/2^256` (`capRound_eq`) | `< 2^-122` (`capRound_lt`); ≈ 2^-123.000 |
| `capPair` | `21 * perElem` | `21N/2^256` (`capPair_eq`) | `< 2^-119` (`capPair_lt`); ≈ 2^-119.608 |

Order and comparison with R1 (Lean):
`capLambda ≤ capRound ≤ capPair` (`capLambda_le_capRound`, `capRound_le_capPair`);
`capPair = RhoSamplerBound.rhoCap` (`capPair_eq_rhoCap`, by `rfl`);
`LiteralClassifier.budget 32 = capPair` (`Caps.budget32_eq_capPair`, by `rfl`),
so `capLambda`, `capRound ≤ LiteralClassifier.budget 32` (`Caps.capLambda_le_budget32`,
`Caps.capRound_le_budget32`); each of the three `≤ PerAttemptEnvelope.B`
(`Caps.capLambda_le_B`, `Caps.capRound_le_B`, `Caps.capPair_le_B`, via R1's
`rho_cap_le`). These are inequalities between numbers; they say nothing about
Aspis's total.

## 5. Validation

Build host, `bash fv_lean.sh <attempt> <Module>` (Lean 4.32.0 against the L187
objects by reference; scope MemoryHigh 6G, MemoryMax 8G, no swap, 180 s
limit). Worktree HEAD when compiled: `01f06debd00` (files untracked; the lead
commits). Wall and peak RSS from `/usr/bin/time -v`; cgroup peak from
`memory.peak`. Swaps 0 in every attempt.

| Attempt | Module | Source sha256 | Exit | Wall | Peak RSS | cgroup peak | Axioms |
|---|---|---|---|---|---|---|---|
| PSB-01 | AspisRowDensityGeneric | e1b8bb9b…a91d6b8ab | 1 | 0.87 s | 1,770,448 KB | 182,239,232 B | `positivity` failed on `((B/n+1 : Nat):ℚ)/B`; `modulo_set_mass_le` had `sorryAx` |
| PSB-02 | AspisRowDensityGeneric | f82ecabb…cf74fa30 | 0 | 1.13 s | 1,776,612 KB | 190,877,696 B | 2 × `[propext, Classical.choice, Quot.sound]` |
| PSB-03 | AspisRowDensityQM31 | c0f466f7…8e68450c0926 | 0 | 4.52 s | 3,499,816 KB | 371,847,168 B | 24 × standard three |
| PSB-04 | AspisRowDensitySampler | 556cd7d7…3ab8370ffd | 0 | 2.72 s | 3,533,132 KB | 370,606,080 B | 10 × standard three |
| PSB-05 | AspisRowDensityCaps | 8aa5e4ab…99e3f3f | 0 | 1.85 s | 3,535,828 KB | 364,785,664 B | 6 × standard three; 2 linter warnings (unused fallback tactic) |
| PSB-06 | AspisRowDensityCaps | d53896874901f9098e4e6930ceb78e334f12e81e51a104f95d79e90e730313ef | 0 | 1.74 s | 3,535,504 KB | 364,548,096 B | 6 × standard three, no warnings |

Full hashes: Generic `f82ecabb6f783d431e652056e56968e276298511138099702f82e476cf74fa30`,
QM31 `c0f466f74362fd81d2aaa3c8db1f2d945e0cf72354d6546936638e68450c0926`,
Sampler `556cd7d7ca803b0a81fcb8ab83a55837205a82a118d3dc367758d33ab8370ffd`,
Caps `d53896874901f9098e4e6930ceb78e334f12e81e51a104f95d79e90e730313ef`
(equal to the worktree masters). PSB-01 → PSB-02: the nonnegativity side goal
proved by `div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)`; nothing else
changed. No warnings in PSB-02/03/04/06; no `sorry`, `axiom`, `decide`,
`native_decide` or raised heartbeats. Numeric facts are closed rational
arithmetic (`norm_num` on numbers of about 2^256), no enumeration.

Imports: Generic: `R0C.ModuloCounting`. QM31: Generic, `R1SelectedChallengeMap`,
`R1RhoSamplerBound`, `AspisFinalSumcheckModel`. Sampler: QM31,
`R1LiteralRhoDensity`. Caps: QM31, `R1PerAttemptEnvelope`, `R1LiteralClassifier`.

## 6. What this does not establish (OPEN)

- The 40-row protocol instance (rows 33 to 39 in a literal transcript whose
  `valid` admits them, a classifier whose `bad`/`budget` dispatch rows 32 to 39
  to these events). The sampler-level theorems assume that instance reuses
  `UnifiedSampler.samp` and a challenge map with `qm31Sample` on rows 33 to 39
  (`hσ`).
- The reads: functions from the Aspis prefix (and row message) to
  `(S_W − claim, S_w − rhs2)`, `(g_b, C_b, c0_b, c2_b)` and `(r0, r1)`, and that
  these are the quantities the model's soundness theorems (`lambda_sound`,
  `round_doom_persists`, `all_zero_of_both_evals_zero_outside_bad2`) are
  applied to. A read returning `none` charges nothing, so the doomed-prefix
  definitions must ensure the read is `some` wherever a start is doomed.
- For row 32: binding of the opened values to the C1, C2 and folded roots
  before ρ, for two families and three trees.
- Transport from the independent-answer law used here to the shared-oracle
  decoded law (`blaw`), which is piece (b)'s dispatcher and R1's decoder chain.
- R1's open byte/field correspondence between Rust `qm31_sample` and
  `qm31Sample`, unchanged.

## 7. Interface for the dispatcher (piece (b)) and the 40-row classifier

All in namespace `AspisRowDensity`; import `AspisRowDensitySampler` (which
imports `AspisRowDensityQM31`) and, for the caps against R1, `AspisRowDensityCaps`.

- Caps: `QM31.capLambda`, `QM31.capRound`, `QM31.capPair : ℚ`; facts
  `QM31.capPair_eq_rhoCap`, `Caps.budget32_eq_capPair`,
  `Caps.cap{Lambda,Round,Pair}_le_B`, `QM31.capLambda_le_capRound`,
  `QM31.capRound_le_capPair`.
- Row 32 in R1's literal transcript (residual pair):
  `Sampler.pair_row32_density read S hS P m hround`, hypotheses
  `hS : ∀ x, (S x).card ≤ 21`, `hround : P.round = 32`; event
  `LiteralOrdinaryDensity.event P m (QM31.setBad read S P)`. With the model's
  set: `S := QM31.pairSet`, `hS := QM31.pairSet_card`.
- Rows 33 to 39 as the `hmass` input of an ordinary-density lift (a copy of
  R1's `LiteralOrdinaryDensity.density` for the 40-row transcript):
  `QM31.combining_mean read S hS n hn c` (`≤ capLambda`),
  `QM31.round_mean read S hS n hn c` (`≤ capRound`), hypotheses
  `hS : ∀ x, (S x).card ≤ 1` (resp. `≤ 2`) and `hn : 32 ≤ n`; or with the
  model's sets `QM31.combining_mean_model`, `QM31.round_mean_model`.
- Rows 33 to 39 directly over `UnifiedSampler.samp`:
  `Sampler.combining_unified_density read S hS p hD i P m hi31 hm hσ`,
  `Sampler.round_unified_density …` (same arguments), with `hσ` from
  `Sampler.selected_sigma_rho i hi` when `p.σ = SelectedChallengeMap.sigma`.
