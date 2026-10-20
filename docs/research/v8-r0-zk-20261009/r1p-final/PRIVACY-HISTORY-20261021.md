# Privacy history split — 2026-10-21

Branch `codex/cx-priv-history-20261021`, base `d93756b49`.

## Stage 1: exact interface split

`QueryScanHistorySplit` separates the **actual** fields of `ScanCoupling`.
`ScanExecution` retains cp, eight coupling-space events and whole-observation
agreement off their union. `ProbabilityContent` is exactly the deleted mass
field. `exact_split` proves equivalence with their conjunction.

There is an obstruction to deleting the mass field with unconstrained events:
`vacuousExecution` supplies an execution join between any two observations
with coupled randomness by choosing all events True. `zero_one_no_scanCoupling`
proves that the constant Boolean observations 0 and 1 have no ScanCoupling.
Thus `probability_not_execution_content` is a compiled counterexample to
recovering that field from the literal execution-only remainder.

A sound interface must fix the events independently of the source join.
`ModelExecutionJoin source model bad` does so, with no probability fields.
Its `toScanCoupling` transports a separately proved model law via cp.meanM;
it does not assume independence between attempts or enumerate any carrier.
This is a usable separation, but it does not assert that the law has been
proved for actual ROM query failures.

Focused env J attempt 9801: exit 0, wall 2.14 s, peak RSS 3,517,108 KiB,
swaps 0; all five theorem audits use only propext, Classical.choice, Quot.sound.
Attempt 9800 retained a local rewrite elaboration failure, fixed by explicitly
instantiating cp.meanM at the event indicator. Complete source revisions,
SHA256, dependency fingerprints, launcher output and timing are in
`history-attempts-9800-9999.jsonl`. New sources/objects only; own drafts are
snapshotted under `snapshots/codex-cx-priv-history-20261021/<attempt>`.

## Stage 2: adaptive shared-oracle histories

`QueryScanIndependentHistory` proves the model-level law that is actually
available on independent coins: the retained LE eight-word, low-18-bit parser
is a measure-preserving projection, eight blocks flatten to 64 independent
words, and reached failure is bounded by `scanProbability`. The reachability
predicate is arbitrary and may depend on every coin. The eight-attempt result
marginalizes the selected attempt by `mean_eval`; it assumes no independence
between the eight failure events. This reuses the existing byte/word bijection
and symbolic first-22 failure-small-range theorem.

These are **unconditional masses of reached-failure subevents**, not masses
conditional on an arbitrary already-revealed shared-oracle history. The latter
is a different statement. Shared-ROM addresses may repeat.

Env J attempt 9805: exit 0, wall 2.24 s, peak RSS 4,028,516 KiB, swaps 0;
six standard-axiom audits. Earlier 9802/9803 were elaboration failures resolved
by explicit equivalence/coordinate arguments and symbolic cardinality
transport; no limits were raised or concrete finite universes reduced.

## Endpoint signature and before/after

The implemented endpoint is deliberately **not** the requested completely
weakened theorem. The unchanged conclusion follows from two execution-only
`ModelExecutionJoin`s, plus a retained `real_model_history_law`. The ideal
mass law is discharged for the fixed `QueryScanIdealHistory.selectedBad`.
The more general `privacy_R1_protocol_history_of_model_laws` adapter retains
both model laws. Neither theorem hides a probability premise inside an
execution definition.

The old arbitrary-event ScanCoupling and a fixed-event ModelExecutionJoin
cannot be asserted to have a strict logical weakening relationship. Event
identification is additional execution content. Literal deletion is strictly
weaker but vacuous, as the zero/one counterexample proves. Therefore no claim
of the requested strict weakening or complete real-model discharge is made.
All other retained binders and the entire conclusion are textually unchanged;
`audit-history.py` checks this and the compiled source hashes.

## Stage 3: compiled shared-ROM obstruction

`QueryScanSharedHistoryObstruction` uses the exact retained transcript grammar:
`squeezeAddress s = ans s ++ [1]`, `advanceAddress s = ans s ++ [2]`.
An advance self-loop `H (advanceAddress s) = s` forces every query state to s
and every query block to the same answer. A symbolic scan induction proves
that scanning repeated copies of one block can accept at most eight distinct
words. Consequently `finish` fails even at the constructed parser's own
`stop done` endpoint. There is no 64-word recurrence evaluation.

`LoopHistory bound` is the existing finite ROM table conditioned on the
advance answer at zero being zero. It is inhabited by the zero table.
`reached_shared_history_failure_mass` proves failure mass **one** on this
history; `reached_shared_history_not_bounded` contradicts the proposed
`scanProbability` bound on every history. For bounds at least 33 this is an
in-domain read, so the phenomenon does not depend on out-of-domain fallback.
The generic `finite_rom_zero_history` induction proves the all-zero history
is reachable in `LazyFrozen.runC` for *every* address program and every ROM
bound, hence also the constructed protocol's full scheduled read program.

This disproves the **conditional-on-every-history** demand, not the existing
unconditional `ScanCoupling.R_rom_query_word_history` field. That field is
only a bound on the mass of each chosen coupling-space event; it does not
quantify conditional probabilities over histories. No claim is made here
that every possible choice of endpoint ScanCoupling is impossible.

The exact missing fact is a source/model join preserving first-read addresses
and answers and identifying a **fresh** 64-word stream outside already charged
collision/prior-read events, together with whole-observation agreement on
those excluded histories or a reduction that pays for them. No Rust fact can
make a retained shared-oracle repeated read fresh. A correct repair must
separate the independent scan failure from collision/prior-read events and
prove where their mass is charged; it cannot assign the entire conditional
self-loop failure the independent-word bound. The existing collision budget
in modelError may support a redesigned combined reduction; this packet does
not silently charge it twice or change the endpoint's error.

Env J attempt 9808: exit 0, wall 2.66 s, peak RSS 4,038,828 KiB, swaps 0;
13 theorem audits, all standard or subsets. 9806 is a green predecessor;
9804 was a variable-substitution elaboration failure. Only this branch's
new module was replaced on the host, with its source/object snapshotted.

## Stage 4: exact first-stop failure and ideal randomness

`QueryScanFirstStopHistory` proves that an error at `stop done q` must be at
the eighth block. Before then, done=true implies either 22 accepted values
(success) or 64 draws, but the symbolic prefix-length bound excludes 64 draws.
The full LE word list is exactly `words64 q`, via the finite-product indexing
bijection. The selected failure therefore implies the existing independent
word failure event. This respects the scanner's check-before-next-word policy,
including completion on a block's final word and exhaustion on the last block.

`QueryScanIdealHistory` splits independent coordinates by a symbolic
bijection, projects `.qb` from transcript coins, and projects those coins from
the exact `fsR1P.IdealRand` retry/tape product. `selectedBad` is the **actual
selected parser error**, not merely a guessed 64-word event. Its mass and
that of any reached subevent are bounded by scanProbability, without any
source hypothesis, counter enumeration, or assumption about the observer.
Uniformity of the programmed table is not used to infer uniformity of
repeated source reads: these are the ideal experiment's independent coins.

Final focused env J results: FirstStop 9817, exit 0, 2.43 s,
4,034,796 KiB, zero swaps, five standard-axiom audits; IdealHistory 9818,
exit 0, 2.36 s, 4,046,436 KiB, zero swaps, seven standard-axiom audits.
9811 was the earlier green ideal-coordinate proof. 9807/9809/9810 exposed
an elaboration issue comparing inferred byte-carrier Fintype instances;
`mean_fintype_transport` proves universe equality extensionally rather than
reducing either enumeration. 9812/9814/9815 were local list/index and
projection elaboration failures, each followed by changed source.

At this point the ideal model's probability content is proved. The source
ideal join must still identify the same selectedBad events and prove the
whole-observation agreement, including programmed-oracle, retry, failure and
publication behavior. Such agreement mentions an arbitrary source experiment
and cannot be a model-only theorem.

## Exact signature diff

```diff
--- PrivacyR1FinalProtocol.privacy_R1_protocol
+++ PrivacyR1FinalProtocolHistory.privacy_R1_protocol_history
@@ -1,3 +1,3 @@
-theorem privacy_R1_protocol
+theorem privacy_R1_protocol_history
     (seed : R1ProverP K CommitHandle Aux F
       (wire base ((base.pubBytes x).length) h B outputs x).toWire)
@@ -26,13 +26,16 @@
     (observer_program : source.Adversary → View K CommitHandle Aux R1Bat →
       List (List UInt8 × OracleAnswer) → OProg)
+    (realBad : source.Adversary → h.Instance → Fin 8 → (fsR1P (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver 8 (by decide) (P_R1 h.transport B hB) (fun h' => VR1 h')).RealRand → Prop)
+    (real_model_history_law : ∀ adv w, h.public w = x.1 →
+      ∀ i, eventMass (realBad adv w i) ≤ scanProbability)
     (R_wire_builder_checker_D75_retry : ∀ (adv : source.Adversary) (w : h.Instance),
-      h.public w = x.1 → ScanCoupling
+      h.public w = x.1 → ModelExecutionJoin
         (realTest h B outputs source adv x w)
         (realTest h B outputs (fsR1P (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver 8 (by decide)
-          (P_R1 h.transport B hB) (fun h' => VR1 h')) (RomObserverBin.observerMap source observer_program adv) x w))
-    (G_sim_R_wire : ∀ adv : source.Adversary, ScanCoupling
+          (P_R1 h.transport B hB) (fun h' => VR1 h')) (RomObserverBin.observerMap source observer_program adv) x w) (realBad adv w))
+    (G_sim_R_wire : ∀ adv : source.Adversary, ModelExecutionJoin
       (idealTestS source adv x (simE h.transport B outputs x))
       (idealTestS (fsR1P (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver 8 (by decide) (P_R1 h.transport B hB) (fun h' => VR1 h'))
-        (RomObserverBin.observerMap source observer_program adv) x (simE h.transport B outputs x))) :
+        (RomObserverBin.observerMap source observer_program adv) x (simE h.transport B outputs x)) (QueryScanIdealHistory.selectedBad)) :
     ZK_FSS h B outputs source x (simE h.transport B outputs x)
       (modelError (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂ + 16 / (2 : ℚ)^486) ∧

```

## Before: original coupling premises, verbatim

```lean
    (R_wire_builder_checker_D75_retry : ∀ (adv : source.Adversary) (w : h.Instance),
      h.public w = x.1 → ScanCoupling
        (realTest h B outputs source adv x w)
        (realTest h B outputs (fsR1P (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver 8 (by decide)
          (P_R1 h.transport B hB) (fun h' => VR1 h')) (RomObserverBin.observerMap source observer_program adv) x w))
    (G_sim_R_wire : ∀ adv : source.Adversary, ScanCoupling
      (idealTestS source adv x (simE h.transport B outputs x))
      (idealTestS (fsR1P (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver 8 (by decide) (P_R1 h.transport B hB) (fun h' => VR1 h'))
        (RomObserverBin.observerMap source observer_program adv) x (simE h.transport B outputs x))) :
```

## After: implemented conditional endpoint, verbatim

The following uses the same namespace opens and context as the original;
`R1Z.QueryScanHistorySplit` is additionally open. It retains the real model
law explicitly because the requested universal history argument is obstructed.

```lean
theorem privacy_R1_protocol_history
    (seed : R1ProverP K CommitHandle Aux F
      (wire base ((base.pubBytes x).length) h B outputs x).toWire)
    (hB : R0Z.K4.PackField B) (hpub : PublicBase F x.1)
    (builder_refinement_D46_D51 : R0Z.HonestValidity.BuilderSoundOn h B x)
    (cF : ℕ)
    (R_commit_equal_fibres : ∀ τ : Tape K F, (Finset.univ.filter
      (fun e : (Fin ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ → OracleAnswer) × (Fin ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ → OracleAnswer) =>
        ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).tapeOf e.1 e.2 = some τ)).card = cF)
    (L₁ L₂ : ℕ) (R_commit_exhaustion : RExh (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂)
    (R_commit_counter₁ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ ≤ 2^64) (R_commit_counter₂ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ ≤ 2^64)
    (R_commit_stream₁ : 16 * L₁ ≤ ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ * 8) (R_commit_stream₂ : 16 * L₂ ≤ ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ * 8)
    (R_wire_coin_carrier : ((wire base ((base.pubBytes x).length) h B outputs x).toWire).Cm ≃ (RIdx → OracleAnswer))
    (R_wire_D80_batches : RWireBatches (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver)
    (R_wire_D80_ordered_log : ∀ (w : h.Instance) (sec : SecP) (d : OracleAnswer)
      (τ : Tape K F) (roots : Fin 3 → OracleAnswer) (rest : RIdx → OracleAnswer) (ch : Challenges K),
      ((wire base ((base.pubBytes x).length) h B outputs x).toWire).comLog (R_wire_coin_carrier.symm rest) roots (view h B outputs x w ch τ) ch =
        (((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).openList ch).map (fun c =>
          (gram (((wire base ((base.pubBytes x).length) h B outputs x).toWire).pubBytes x) ((wire base ((base.pubBytes x).length) h B outputs x).toWire).vtag (((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).leafVal h w x τ ch) sec d rest
            (cposOf (E₁ := ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁) (E₂ := ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂) c), ansC roots rest c)))
    (R_commit_cell_count : RCommitCount L₁ L₂)
    (R_commit_blocks₁ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ ≤ 2 * L₁) (R_commit_blocks₂ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ ≤ 2 * L₂)
    (source : FSExperiments K CommitHandle Aux R1Bat F)
    [Fintype source.RealRand] [Nonempty source.RealRand]
    [Fintype source.IdealRand] [Nonempty source.IdealRand]
    (observer_program : source.Adversary → View K CommitHandle Aux R1Bat →
      List (List UInt8 × OracleAnswer) → OProg)
    (realBad : source.Adversary → h.Instance → Fin 8 → (fsR1P (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver 8 (by decide) (P_R1 h.transport B hB) (fun h' => VR1 h')).RealRand → Prop)
    (real_model_history_law : ∀ adv w, h.public w = x.1 →
      ∀ i, eventMass (realBad adv w i) ≤ scanProbability)
    (R_wire_builder_checker_D75_retry : ∀ (adv : source.Adversary) (w : h.Instance),
      h.public w = x.1 → ModelExecutionJoin
        (realTest h B outputs source adv x w)
        (realTest h B outputs (fsR1P (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver 8 (by decide)
          (P_R1 h.transport B hB) (fun h' => VR1 h')) (RomObserverBin.observerMap source observer_program adv) x w) (realBad adv w))
    (G_sim_R_wire : ∀ adv : source.Adversary, ModelExecutionJoin
      (idealTestS source adv x (simE h.transport B outputs x))
      (idealTestS (fsR1P (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver 8 (by decide) (P_R1 h.transport B hB) (fun h' => VR1 h'))
        (RomObserverBin.observerMap source observer_program adv) x (simE h.transport B outputs x)) (QueryScanIdealHistory.selectedBad)) :
    ZK_FSS h B outputs source x (simE h.transport B outputs x)
      (modelError (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂ + 16 / (2 : ℚ)^486) ∧
    modelError (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂ + 16 / (2 : ℚ)^486 ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454
```

## Stage 5: unconditional scan-subrun obstruction

`QueryScanSharedHistoryMass` strengthens the counterexample without conditioning
the oracle table: for every bound≥33, a scan **started at a fixed zero state**
against a uniform table fails with mass at least `1 / card OracleAnswer`.
The self-loop event has exactly this mass, by a generic coordinate projection.
The retained symbolic `card_ans` theorem gives `card OracleAnswer = 2^256`;
thus this lower bound is strictly greater than scanProbability≤2^-486.
`uniform_shared_scan_not_independent_bound` is the compiled contradiction.
This result concerns the query subrun at a fixed input state. It is **not**
a lower bound for the complete release game's differently distributed starting
state, nor a proof that every endpoint ScanCoupling is impossible. It rules
out the proposed generic transfer from uniform shared-ROM tables to the
independent scan bound without collision accounting.

Env J 9821: exit 0, 2.28 s, peak RSS 4,047,480 KiB, swaps 0, eight standard
axiom audits. 9820 encountered inferred byte-carrier instance reduction;
the replacement factors evaluation/point-mass transport through generic
carriers and reuses card_ans via Fintype subsingleton equality. No enumeration,
cap increase, recursion override, or unchanged retry was used.

## Exact remaining source and model facts

| Obligation | Proven here / exact remaining fact |
|---|---|
| At most eight attempts per model side | Existing model uses `Fin 8`; new laws quantify each of those coordinates. Source cannot silently add attempts: the execution join must cover its complete run and publication. |
| LE low-18-bit words, first 22 distinct, stop/failure | Retained byte-word bijection plus new MP projection and symbolic selected-stop/failure bridge. Source must identify its parsed words, masks, state updates, stable order, first stop, and error count with these exact functions. |
| Ideal model mass | Proved for `selectedBad` on the exact constructed `fsR1P.IdealRand`, including arbitrary reached subevents. |
| Real model mass | `real_model_history_law` remains explicit. Need a concrete definition of the real bad events and a valid unconditional bound, using fresh lazy words with collision/prior-read transport. The generic shared-ROM bound is false; a combined reduction must charge collisions once within its stated budget. |
| Every history conditional bound | False as stated: inhabited self-loop histories have failure mass one. No source fact can repair this universal model claim while preserving shared-oracle repeated-read semantics. Restrict to fresh histories, use reached subevent masses, and charge the excluded events. |
| Coupling maps | Source must supply genuine finite randomness and measure-preserving maps to this same constructed experiment. No Rust extraction/fixture is assumed to give these maps. |
| Whole Boolean agreement off the union | Remains exactly `ModelExecutionJoin.agreement`. Source must preserve complete observations, retries, partial/failed query decoding, mask exhaustion, programmed/common backend answers, ordered logs, serialization, and failure publication. Model-only facts cannot establish an equality mentioning an arbitrary source observation. |
| Event ownership | Source join must identify the selected model events or explicitly transported lazy events, not select arbitrary exceptional predicates. Literal mass-field erasure allows True everywhere and is insufficient. |

The two fixed-event joins have **no probability fields**. The real law is a
separate, plainly named input. This is an honest split and an ideal discharge,
not the requested complete replacement by strictly weaker joins. The report's
compiled counterexamples are the reason that item stops; independent ideal,
parser, endpoint adapter, and evidence work continued through completion.

## Endpoint and resource evidence

`PrivacyR1FinalProtocolHistory.privacy_R1_protocol_history` retains exactly the
original ZK_FSS conclusion and numerical error. It supplies the ideal selected
failure law internally. The generic adapter also compiles. The new endpoint
is independently audited by `#print axioms`; final receipt appears below.

All attempts use run-joint.sh env J, Lean -M7000, MemoryHigh=5G,
MemoryMax=7G, MemorySwapMax=0, and the launcher's aggregate reservation check.
Only new modules and this branch's own snapshotted drafts/objects were written
in the shared build tree. No existing dependency source/object was replaced.
Protected endpoint, BuilderSource and SourceIdentification sources match base.
No Rust harness, wallet, account key, production file, merge, push, SBF build,
or unrelated full regression was touched. The focused endpoint is the final
dependent bridge; no frozen certificate or manifest was changed, so no
unchanged package-wide replay was run.

Final endpoint env J 9822: exit 0, wall 7.01 s, peak RSS 4,058,352 KiB,
swaps 0; all three audits `[propext, Classical.choice, Quot.sound]`.
9813/9819 were green adapter predecessors; the final change specializes the
named ideal-history theorem to the actual selected parser error. No old
source or object was replaced; only the branch's new endpoint was updated.

`python3 r1p-final/audit-history.py` passes: 23 assigned attempts, seven final
modules, 48 theorem audits, all final source SHA256 and independent launcher
SHA pins matching, no duplicate source/dependency pairs, zero swaps throughout,
and only standard axioms in every final receipt. It also verifies the current
direct dependency object hashes, records object SHA256/size without binaries,
checks protected sources against d93756b49, validates the endpoint generator
with `--check`, and matches the quoted before/after statements against source.
`history-final-audit.json` contains these pins and the final target metrics;
`history-attempts-9800-9999.jsonl` preserves full outputs, errors, timings,
source revisions, source hashes and dependency fingerprints for every attempt.

What remains open is the real model's unconditional history/event law with
collision/prior-read accounting and both source execution joins. The requested
per-every-history bound and literal probability-field erasure have compiled
counterexamples. The complete execution-only replacement is not claimed.
