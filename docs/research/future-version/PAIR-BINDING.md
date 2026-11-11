# The residual pair under the batching challenge: binding before ρ

> **Correction after independent reading, 2026-11-11 (one-transaction game note, section 0).** The
> finding that R1 already binds all three trees is true in substance, but the modules cited for it
> below are not the ones R1's bound uses. The bound reaches the recovery through
> `OraclePortFrozenOrder.authenticated` (OraclePortFrozenOrderSelectedRecovery.lean), which
> recovers through an in-place slot program. `OraclePortAllSelectedRecoveryC6.authenticated` and
> `OraclePortRecoveredAcceptanceC6.accepted_checks` belong to an earlier draft chain: they are in
> the closure but, as far as that reading went, not used by the bound at theorem level. Both
> versions have the same conclusion and the same collision event. See ONE-TRANSACTION-GAME.md
> sections 0 and 3.2.

Status, 2026-11-11. Research note for the Aspis one-transaction verifier
(`verify_summed_format`, crates/aspis-r1-cost-probe/src/fused.rs). It addresses
the item SOUNDNESS-ARGUMENT.md section 3 and section 8 (a) leave OPEN: that
the pair of residual vectors combined by the batching challenge ρ is fixed
before ρ for every accepting run, with all three trees bound, and which
binding event that costs. "R1" is the existing two-transaction verifier and
its Lean development (the L187 closure). No security figure is quoted for
Aspis and none of R1's is restated.

**Result in one paragraph.** No attack was found and no new binding event is
needed. In R1's model the committed values of all three trees already exist
as transcript objects (C1 word in row 0, C2 word in row 2, folded word in
row 30), R1 already proves that opened C1, C2 and folded values at the
queried positions equal those committed words outside one collision event,
and R1 already transports its per-query checks along that identification.
The Aspis residual pair is a function of exactly the per-query record R1
transports, so the same identification carries it. What is new and proved
here (model level, Lean, standard axioms): the pair bad set, its 21-element
bound, the deterministic bridge with R1's `queries_match` recovered as a
special case, the transport of the pair, the merged-multiproof form of R1's
opening recovery, the row-32 density at R1's cap, and the row 31/32 terminal
step. What is not established: the source refinements on the Aspis path
(merged multiproof, batched fold sums), the Aspis instance of R1's
stored-decision/acceptance chain, the Aspis read count that sets the
collision budget, and the 40-row protocol instance that would consume the
row-32 density. Section 6 lists them.

## 1. R1's statement, quoted

`AspisR1.QueryResidualBridge` (R1QueryResidualBridge.lean), with section
variables `{K E : Type} [Field K] [Fintype K] [Field E] [Fintype E]
[DecidableEq E] [Algebra (ZMod P) E]`:

```lean
def values (d : Data E) (q : Fin 22 → Fin 262144) : Fin 22 → E :=
  fun i => curveValue (AspisR1.SecondFoldRestoration.channels d.V) d.alpha1
    (AspisR1.parentIndex (q i))

def residuals (d : Data E) (q : Fin 22 → Fin 262144) : Fin 22 → E :=
  fun i => values d q i -
    AspisR1.ConcreteProjection.secondEncoder d.f (AspisR1.parentIndex (q i))

def rhoBad (iota : K →+* E) (d : Data E) (q : Fin 22 → Fin 262144) : Finset K :=
  AspisR1.ResidualBatch.bad iota (residuals d q)

theorem rhoBad_card (iota : K →+* E) (d : Data E) (q : Fin 22 → Fin 262144) :
    (rhoBad iota d q).card ≤ 21

theorem queries_match (iota : K →+* E) (d : Data E)
    (q : Fin 22 → Fin 262144) (rho : K)
    (hrho : rho ∉ rhoBad iota d q)
    (hfirst : ∀ i, match0 d (q i))
    (hbatch : ∑ i : Fin 22, (iota rho) ^ i.val * residuals d q i = 0) :
    ∀ i, q i ∈ matchingSet d

theorem false_claims_query_containment (iota : K →+* E) (d : Data E)
    (q : Fin 22 → Fin 262144) (rho : K)
    (hgood : Good d) (haccepted : AcceptedPairing d) (hnot : ¬ Claims d)
    (hrho : rho ∉ rhoBad iota d q)
    (hfirst : ∀ i, match0 d (q i))
    (hbatch : ∑ i : Fin 22, (iota rho) ^ i.val * residuals d q i = 0) :
    (matchingSet d).card ≤ 9557 ∧ ∀ i, q i ∈ matchingSet d
```

plus `accumulated_false_claims_containment` and
`recurrence_false_claims_containment`, which replace `hbatch` by the
closed-sum equation `∑_j f_j · iota(∑_i ρ^i basis_{i,j}) = ∑_i ρ^i values_i`
and by the 22-step recurrence. Every hypothesis: `hrho` (ρ outside the
residual set), `hfirst` (R1's per-query first-fold equality, `match0 d i :=
foldWord α0 (batchedWord W γ) i = V i`), `hbatch` (the batched second-fold
equation), and for containment `Good d` (γ ≠ 0 and γ, κ, α0, α1 outside
their bad sets), `AcceptedPairing d` (final dot product and two boundary
equations), `¬ Claims d`. The file header says it: "Deterministic
connection ... the probability law and distinct-query sampler are separate
obligations." **`QueryResidualBridge` is not a binding theorem.** It is an
algebraic statement about fixed `Data`. Fixedness before ρ and binding live
elsewhere in R1:

- Fixedness: the row-32 classifier event `LiteralRhoDensity.bad P v`
  (R1LiteralRhoDensity.lean) reads `(d, q)` from the literal prefix `P`
  through `LiteralRhoDensity.read P := do let d ← LiteralMatchingData.beforeRho P;
  let q ← LiteralQueryRead.queriesAt P.rounds 31; pure (d, q)`, and is
  `rhoOf v ∈ rhoBad eK d q`; `row32_density` bounds it by `rhoCap`
  (`21·(⌊2^256/P^4⌋+1)/2^256 < 2^-119`). `LiteralRhoBinding.rho_event_iff`
  identifies the classifier's row-32 event with this predicate.
- Binding: section 4 below.

## 2. What plays "the committed values"

In R1's literal transcript (R1LiteralTranscript.lean) the three
commitment-bearing messages carry words:

```lean
inductive Message
  | initial (root : State) (word : C1Word)   -- row 0
  | payload (bytes : BytesMessage)
  | c2 (bytes : BytesMessage) (word : C2Word) -- row 2
  | second (bytes : BytesMessage) (word : VWord) -- row 30
```

`MatchingSupport.Data` takes `W : Fin 29 → InitialWord E` from the C1 and C2
words (`LiteralTypedWords.word embed eK c1 c2`, lanes 0..25 and 28 from C1,
26 and 27 from C2) and `V : FinalWord E` from the row-30 word
(`LiteralMatchingData.read`). In the release chain these words are the
words recovered from the oracle log cut at each root's first commitment
frame (`OraclePortRecoveredAcceptanceC6.maps`: `recovered log (frames k) p k`
for `k = 0, 1, 2`, i.e. `BinRawByteCutStability.recoverAt (tag k) (width k)
(cut log frame) (slots 18 i) (committedRoot p k)`, tags 0x71/0xf1/0x72,
widths 480/128/128).

So for the folded tree the committed object is `V`; **the same object exists
for C1 and C2**, as `W`, at every position including the queried fibres.
R1 needs it for C1 and C2 for two reasons: `match0` (R1's per-query
first-fold check) reads `W` at the fibre of `q i`, and the earlier bad sets
(`gammaBad d.W …`, `firstBad d.W …`) are sets of the committed `W`.

## 3. The proposed statement, next to R1's

New definitions (AspisPairResidualBridge.lean, namespace `AspisPairResidual`):

```lean
def firstResiduals (d : Data E) (q : Fin 22 → Fin 262144) : Fin 22 → E :=
  fun i => FirstFold.foldWord d.alpha0 (TwoFoldExtraction.batchedWord d.W d.gamma) (q i)
             - d.V (q i)
def pairBad (iota : K →+* E) (d : Data E) (q : Fin 22 → Fin 262144) : Finset K :=
  AspisFuture.StageD.bad2 iota (firstResiduals d q) (QueryResidualBridge.residuals d q)
```

`bad2 r0 r1` is the K-roots of `Σ r0_i T^i` if that polynomial is nonzero,
else of `Σ r1_i T^i` if nonzero, else empty (StageDSumcheck.lean).
`firstResiduals d q i = 0 ↔ match0 d (q i)` (`firstResidual_eq_zero_iff`).

| | R1 `queries_match` | Aspis `pair_queries_match` |
|---|---|---|
| carriers | `iota : K →+* E`, `d : Data E`, `q : Fin 22 → Fin 262144`, `rho : K` | identical |
| exceptional set | `rho ∉ rhoBad iota d q` | `rho ∉ pairBad iota d q` |
| first fold | `hfirst : ∀ i, match0 d (q i)` (22 equalities) | `h0 : ∑ i, (iota rho)^i * firstResiduals d q i = 0` (one equality) |
| second fold | `hbatch` | `hbatch`, the same |
| conclusion | `∀ i, q i ∈ matchingSet d` | identical |
| quantifiers | all outermost universal; no change | same |

`pair_false_claims_query_containment` and
`pair_accumulated_false_claims_containment` are the corresponding forms of
R1's containment theorems (`Good`, `AcceptedPairing`, `¬ Claims` unchanged;
the closed-sum form takes the verifier's `lhs1 = rhs1` for the first fold,
`batched_first_iff`).

Differences, spelled out. (1) One premise is weakened: 22 equalities become
one batched equality; the price is the exceptional set. (2) The exceptional
set changes: `pairBad` equals `rhoBad` whenever every first-fold residual is
zero (`pairBad_eq_rhoBad_of_match0`); when some first-fold residual is
nonzero it is the root set of the first-fold polynomial, a set R1 never needs
because R1 rejects such a run outright. Both have at most 21 elements
(`pairBad_card`). (3) Nothing else changes: same data, same queries, same
conclusion. (4) R1 recovered: `queries_match_from_pair` re-derives R1's
`queries_match`, with R1's exact hypotheses, from the pair theorem. (5) The
pair theorem is proved through R1's `queries_match`, not beside it.

## 4. Binding events per tree, and where R1 charges them

All three trees rest on one event: `AllAddressCollision.bad iv
BinRawByteCollisionTargets.pred Q` on the oracle log (five targets: the two
binary-child parsers, the trailing root reader, the offset-38 root reader,
the leading duplex state; BinRawByteCollisionTargets.lean). Its mass is
`BinCombinedMerkleCollision.kappa Q = 6Q²/256^32`
(`BinRawByteCollisionTargets.mass`), the collision term of R1's bound
(`R1FinalSoundnessBinPerQuery.final_soundness` instantiates it at `Q + 1161`;
SOUNDNESS-ARGUMENT.md section 6.3).

| Tree | Root absorbed (code) | Frame reader | R1 theorem fixing the opened value |
|---|---|---|---|
| C1 | init, `prefix.c1_root` (r1_semantic.rs:347) | trailing, `pred 2` | `OraclePortAllSelectedRecoveryC6.authenticated`, kind 0 |
| C2 | row 2 payload (r1_semantic.rs:347) | trailing, `pred 2` | same, kind 1 |
| folded | row 30, `OFF_FOLDED_ROOT..OFF_ROUND1` (candidate.rs:124, verifier.rs `Prepared::new`) | offset 38, `pred 3` | same, kind 2 |

`authenticated` concludes, for every `pos < 22` and `kind < 3`,
`recovered log frame p kind (index q kind pos) = some (payload p kind pos)`
under: accepted batch verification, log consistent with `H`, verifier reads
in the log, `firstReads ≤ Q`, no collision event, frame read with
`pred j frame = some (committedRoot p kind)`.
`OraclePortRecoveredAcceptanceC6.accepted_checks` applies it for all three
kinds and transports R1's per-query checks to the cut-recovered words through
`OraclePortSelectedObservationsC6.observe_withWords`. That chain is on the
import path of the release top `TAS_FinalB` (… `OraclePortStoredProbabilityC7`
→ `StoredConsumerC7` → `StoredReductionC7` → `StoredAcceptanceC6` →
`CanonicalAcceptanceC6` → `ActualAcceptanceC6`) and is used at theorem level
in `OraclePortCanonicalAcceptanceC6` line 83. (Import-graph check over the
13,552 flat files; the source-level FJp route separately recovers the folded
tree only, `FJo_RecoveryAt`, for its own purpose.)

Transport of the pair (AspisPairResidualObservation.lean): the pair is a
function of R1's observation record (`pair_eq_pairOf`: `firstResiduals` is
`first − opened`, `residuals` is `second − secondEncoder f`), so it is
unchanged under `withWords d W V` whenever `W`, `V` agree with `d` on the
queried initial fibres, the queried folded values and their folded fibres
(`pair_withWords`, `pairBad_withWords`) — exactly the three premises R1
discharges from the three-tree recovery. `transport_pair` carries both
batched equalities from the opening words to the committed words and, off
the committed words' `pairBad`, gives all 22 `match0` and all 22 zero
residuals for the committed words.

Code check, all values entering either residual: `fold_sums` reads C1 bytes
`0..480` of each opening (26 base lanes, 4 bytes each, and the QM31 tail
lane at 104, four slots of 120), C2 bytes `480..608` (two QM31 lanes, four
slots of 32) and folded bytes `672..800` (four QM31 values); these are
exactly R1's leaf payloads (`typedRows`: kind 0 `take 480`, kind 1
`slice 480 128`, kind 2 `slice 672 128`), salts at 608, 640, 800. Everything
else in either residual is transcript-derived: γ powers (row 27), α0 (29),
α1 (30), the final message (31), the query geometry (31), ρ (32). The roots
the merged multiproofs check are `p.roots[0]`, `p.roots[1]` (absorbed in the
semantic rows) and the folded root read from the same bytes row 30 absorbs.
All three precede the query derivation (row 31) and ρ (row 32) in
`Prepared::new`.

**No new term appears**, provided (a) the Aspis read count stays within the
budget the collision term is evaluated at (SOUNDNESS-ARGUMENT.md 6.3: 1,112
verifier-core reads, on paper, against R1's 1,161) and (b) the merged
multiproof refines R1's multiproof relation (section 6). The pair adds no
binding read: the same 22 openings per tree are authenticated as in R1.

## 5. Attempt to break it

**Attack 1: open C1 or C2 differently after ρ.** The adversary sees ρ and
wants a different `(packed', salt')` at a queried index `i` of C1 that still
authenticates under the root absorbed at init, to make a nonzero first-fold
residual vector cancel at ρ (the teeth vector
`rho_dependent_cancellation_passes_the_batched_check_and_fails_the_pinned_one`
shows the arithmetic cancellation is easy once residuals can depend on ρ).
In the model: an accepted merged multiproof gives an accepted single path for
`i` (`BinMultiproof.accepted_path`), and
`BinRawByteCutRecovery.recover_at_first_commitment` then says the opened leaf
is the one recovered from the log strictly before the root's commitment
frame. `AspisPairResidual.Merkle.no_second_opening` states the attack's
failure directly: two accepted multiproofs under the same root in the same
log, each binding a leaf at `i`, bind the same `(packed, salt)`, unless the
collision event. The recovered leaf is a function of the log before the
frame, which precedes the ρ block (the duplex chain). Charged probability:
the collision event, `kappa` at the run's read budget, counted once for the
whole run, not once per tree or per opening.

**Attack 2: duplicate folded indices.** Two queries with the same parent
`u/4` read the same folded leaf. `merged_tree` rejects equal indices with
different leaf hashes (fused.rs:783); with equal hashes, recovery at that
index gives one value, so both openings are equal outside the collision
event (`no_second_opening` with `active = active'`).

**Attack 3: residual inputs outside the leaves.** None found (section 4,
code check). The 832-byte opening's remaining bytes are the three salts,
inside the leaf hashes.

**Attack 4: the bad set chosen too late.** The row-32 event reads `(d, q)`
from the completed prefix through R1's reader (`AspisPairResidual.Row32.bad`);
the prefix rows 0–32 of the Aspis transcript are byte-identical to R1's
(SOUNDNESS-ARGUMENT.md section 2), so the reader and its fixedness argument
are R1's.

**Attack 5: the first-fold family is no longer checked per query, so the row-31
query event loses its matching premise.** R1's row-31 event is "support
≤ 9557 and every query in it"; R1 already needs row 32 to put the queries in
the support (`match1`). Aspis needs row 32 for `match0` as well.
`AspisPairResidual.Support.large_support` is the Aspis form of R1's
`LiteralQueryRhoSupport.large_support`: no hit at row 31, no hit of the pair
event at row 32 and the two batched equalities give support ≥ 9558.

Verdict: not the V8 B1/B2 situation. The family combined by ρ is a function
of objects fixed before ρ (committed words read from the prefix, transcript
challenges, queries), the identification of opened with committed values is
R1's existing theorem under R1's existing event, and the deterministic
bridge is proved. The remaining risk is in the source refinements below,
not in a missing binding theorem.

## 6. Open items (none is an assumption; none is closed here)

1. **Merged multiproof refinement.** `multiproof::verify_counting_merged`
   with `merkle_verdict` and `merged_tree` (fused.rs:776–806) must refine
   `BinMultiproof.PaddedAccept H root 18 active v count capacity stored trace`
   on the distinct sorted index set, with `BinMultiproof.Dedup` from the
   duplicate rule, R1's leaf input `leafInput tag packed salt`, and every
   issued hash input in the log. Smallest R1-side lemma: that refinement for
   one tree (the algorithm is `verify_counting_direct` with `MAX_MERGED = 22`;
   `BinMultiproof` is index-set generic). With it,
   `merged_query_recovery` gives R1's `recovered … = some (payload …)` form.
2. **Aspis acceptance chain.** An Aspis instance of R1's stored decision and
   `accepted_checks` (C6) whose typed checks are the two batched equalities
   (not `Writer`), feeding `transport_pair` and then `large_support`.
3. **Batched fold sums refinement.** `fold_sums` computes `Σρ^i F_i`,
   `Σρ^i b_i`, `Σρ^i G_i` for the R1 model quantities (TESTED, OPEN;
   SOUNDNESS-ARGUMENT.md section 9).
4. **Read count.** The collision term is evaluated at the run's first-read
   budget; the Aspis count (1,112 verifier-core reads, on paper) must be
   proved and the account path counted (SOUNDNESS-ARGUMENT.md finding 5).
5. **Protocol instance.** The 40-row decoder and classifier; the row-32 event
   and density below are ready to plug in.

## 7. Interface for the row-32 density

```lean
-- AspisPairResidualDensity.lean, namespace AspisPairResidual.Row32
def bad (P : LiteralTranscript.Prefix) (v : AspisWideTower.WideExact) : Prop :=
  match LiteralRhoDensity.read P with
  | none => False
  | some (d, q) => SelectedChallengeMap.rhoOf v ∈
      AspisPairResidual.pairBad LiteralOpeningView.eK d q
```

Classifier entry at round 32: `LiteralOrdinaryDensity.event P m
(AspisPairResidual.Row32.bad P)` (R1's entry with `LiteralRhoDensity.bad`
replaced). Cardinality: `AspisPairResidual.pairBad_card : (pairBad iota d
q).card ≤ 21`. Density: `AspisPairResidual.Row32.row32_pair_density P m
(hround : P.round = 32) : independentMean (LiteralTranscript.samp P.round P
m).toProgram (fun v => indicator (LiteralOrdinaryDensity.event P m (bad P)
v.2)) ≤ RhoSamplerBound.rhoCap`, the same cap and budget entry as R1's row 32
(`LiteralClassifier.budget 32`). R1 check: `bad_iff_r1_of_match0` (equal to
R1's event when the prefix data satisfy every `match0`). The prefix type is
R1's; a 40-row decoder must present rows 0–32 as this prefix (they are
byte-identical) or re-state the reader on its own prefix.

## 8. Lean files and compiles

Masters in docs/research/future-version/lean/, compiled on the build host
with `fv_lean.sh` (Lean 4.32.0, scope MemoryHigh 6G, MemoryMax 8G,
MemorySwapMax 0, 180 s limit) against the L187 objects. Source revision:
untracked files on branch future-version at 9dc8c67b9af. Every `#print
axioms` result: `[propext, Classical.choice, Quot.sound]`. No `sorry`,
`axiom`, `native_decide` or raised heartbeats.

| Attempt | Module | sha256 (source) | Exit | Wall | Peak RSS (time -v) | cgroup peak | Swaps |
|---|---|---|---|---|---|---|---|
| PSC-01 | AspisPairResidualBridge | 701c8a76…c3b9aa | 0 | 3.51 s | 3.08 GB | 0.33 GB | 0 |
| PSC-02 | AspisPairResidualObservation (first version) | fdd04f42…070994 | 1 | 19.3 s | 4.20 GB | 0.43 GB | 0 |
| PSC-03 | AspisPairResidualMerkle | 6e751d1c…8528b5 | 0 | 1.18 s | 1.79 GB | 0.19 GB | 0 |
| PSC-04 | AspisPairResidualDensity | 44d005ac…7adb | 0 | 3.84 s | 3.53 GB | 0.37 GB | 0 |
| PSC-05 | AspisPairResidualObservation | a81c216e…851cfd | 0 | 5.76 s | 4.22 GB | 0.45 GB | 0 |
| PSC-06 | AspisPairResidualSupport | 6c07c0ed…ed3aa4 | 0 | 4.71 s | 3.55 GB | 0.38 GB | 0 |

PSC-02 failed on a `rfl` that hit the default heartbeat limit in `isDefEq`
(unfolding R1's fold definitions) and on two name ambiguities; replaced by an
explicit unfold under local irreducibility, as R1's own files do (PSC-05).
PSC-01 prints two unused-section-variable linter warnings
(`batched_first_iff`, `residualPolynomial_same`); no other warnings.
"Peak RSS" from `time -v` includes the mapped L187 objects; the cgroup peak
is the scope's charged memory.

Kinds of theorem: all are model theorems in R1's model (algebra over
`Data`; R1's Bin commitment model; R1's literal classifier model). None is a
source-helper theorem, a source-to-model refinement, a composed security
theorem, or connected to the frozen release artifacts.
