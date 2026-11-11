# PIN2 close-out: four read-only checks (2026-11-11)

Read-only. Nothing was edited or compiled. Release sources were read from origin/research in
/Users/dominic/ZK; PIN2 sources from branch fix/pin2-lean-20261110 at c8b641cae0e. "Reachable" below means
membership in the committed walker lists of constants reachable from the release headline:
evidence/replay-l187-20261109/final/L187_AX2_charge/audit/NEP_proof0_AspisR1.TAS_FinalB.deployed_charge_REACHABLE.txt.xz
(146,551 constants) and evidence/integrate-20261111/NNH_L942/audit/NEP_proof0_AspisR1.TAS_FinalB.deployed_splitB_REACHABLE.txt.xz
(146,370 constants). Decompressed copies are in /private/tmp/claude-501/-Users-dominic-ZK/3db59790-41f3-4c53-ae90-3fc42a8cab96/scratchpad/closeout-reach.

## 1. Headline text under PIN2: byte-identical; not yet recompiled; dependencies changed

- Release source: evidence/integrate-20261111/TAS_FinalB.lean, sha256 ed99757ca77401e97d9a517ae908972fdc28595a405e02c2fa8f17d3f97dbf07.
  The same hash appears in the L187 replay batch evidence/replay-l187-20261109/batches/B0080/batch.json and in the
  NNH_L939 receipt. The branch HEAD copy has the same hash, and so does the scratchpad copy TAS_FinalB.lean.
  (TAS_FinalB_run6.lean, 64060e19…, is the older run-6 L927 text.)
- PIN2 handover sources: the branch has 710 distinct .lean names under pin2-*/sources (pin2-public-binding, w3a, w3b,
  w3c, w4, w5, w6, w7; w8 has no sources dir). None of them is TAS_FinalB, NNH8_*, *HeadlineB*, RSL_EVB/EVB_EventB,
  F3T_Numeric, NHZ_SameLaw or NDO_Rc7_Top. `git diff --name-only <merge-base f168fce> HEAD` touches none of these modules.
- Host plan: pin2-w3a-20261111/HOST-REBUILD-ORDER.tsv:10593 reads `10592 TAS_FinalB blocked:W3b+devnet+StreamC see release closure`.
  NNH8_Top (:10589), NNH8_Exec (:10550), NNH8_Charge (:10558), NHZ_SameLaw (:7342), NDO_Rc7_Top (:5244) and
  RPz7_F3T_Numeric (:3405) carry the same "see release closure" source entry. So the host compiles the release text.
- No PIN2 overlay contains an object for these modules yet. /Users/dominic/aspis-lead-infra/l187-closure/overlay-PIN2,
  -PIN2-W4, -PIN2-W7 and -PIN2-W8 have no TAS_FinalB, NNH8_*, NHZ_SameLaw, NDO_Rc7_Top or F3T_Numeric object. Only objs/ (L187) and
  overlay-HOST-P1 (pre-PIN2) have them. The PIN2 replay of the headline has not been recorded on the branch.
- Verdict: TAS_FinalB is byte-identical to the release, including `deployed_splitB` (TAS_FinalB.lean:94-118) and
  `deployed_charge` (:153-183). The text does not settle the meaning, though. Its constants unfold through definitions that
  PIN2 changed. Examples: pin2-w7-20261111/CHANGES.tsv:89 (`LIB_VPublicTranscript.code` is now `publicTranscriptPIN2`;
  PIN2-W10-REPORT.md:23 says "The top statement (`TAS_FinalB.deployed_splitB`) names `NNH_Libraries.VL`" and reaches it),
  and the restated cone modules RPz7_F3T_ByteCarrier and RPz8_F3T_Semantic (pin2-w7-20261111/sources). The kernel
  statement has to be re-compared after the PIN2 host build. Identical source text is not evidence of an identical
  statement.

## 2. Averaging step for max r (indicator ¬Outcome): stated, not compiled in the headline chain

- The remark is in evidence/event-b-20261107/EVB_EventB.lean:289-299 (sha256 43645d9f…, the copy used by L187 batch B0017):
  "The deployed per-world loss `max r (indicator ¬Outcome)` then satisfies the SAME pointwise inequality, so its mean is at
  most `total (Q0+Q1)`: E_rec is charged once. (The averaging step for `max r _` is a host restatement of
  `F3U_Averaging.charge`; it is not compiled here.)" Only the pointwise lemma `RSL.EVB.no_second_charge` (:300) is proved.
- What the headline proves (TAS_FinalB.lean:162-178, via NNH8_ChargeOf.deployed_charge_of, evidence/integrate-20261111/NNH8_Top.lean:229-274):
  (i) pointwise in H, `max (0:Rat) (ind (Runs … ∧ ¬ OutcomeRec …)) ≤ ind (E_rec at eval H fixedProgram)`;
  (ii) `lazyMean fixedProgram emptyTable (indicator E_rec) ≤ F3T_Numeric.total (Q0+Q1)`;
  (iii) for each H, `failureModel (runtime …) ≤ total (Q0+Q1)`.
  The proof instantiates `NNH8_DeployedOuterOf` with r = m = 0 (NNH8_Top.lean:261-263). Its docstring
  (NNH8_Top.lean:226-228) says: "No expectation on an arbitrary World-dependent indicator is invented."
- The averaging that is compiled covers only the runtime mass r. `FJp_Mass.bounded` (reachable) proves
  `F3T_Runtime.deployedFailure runtime ≤ lazyMean model failureMass + accountLoss` by `F3U_Averaging.charge` (reachable).
  No reachable theorem averages `max r (ind fail)` or the World-dependent failure indicator over H.
- Two non-host versions exist, and neither is in the headline cone:
  - `RSL.TASB.deployed_charge` (evidence/top-assembly-20261107/TAS_TopB.lean:220-248) concludes
    `Ex.E (fun H => max (r H) (ind (Runs … ∧ ¬ hb.OutcomeRec …))) ≤ T`. It is stated over an abstract
    `Ex : Expect X.Oracle` with `budget` as a hypothesis. TAS_TopB is in the closure, but this theorem is not reachable.
  - `AspisR1.NNC_NoSecondCharge.average` (evidence/root0-weak-20261111/NNC_NoSecondCharge.lean:29-58) is generic: `attack`
    must be a predicate of `eval H execution` for a fixed program. NNC_NoSecondCharge is outside the release closure.
- Verdict: the averaging step is stated but not compiled. The headline gives a pointwise inclusion plus a mean bound on
  E_rec. "Pr[accepted ∧ ¬Outcome] ≤ total" needs a further step, and that step must express the wOf-dependent failure as a
  function of a program view, which is exactly what F3U_Averaging.charge requires. That step is not a theorem.

## 3. The 2,322 term: the sibling reading is right; the draft's campaign sentence over-counts (conservative, mislabelled)

- Derivation: lean/F3T_Bounds.lean:41-52, `log_length … : (eval H (recorded D build P)).1.length ≤ Q+2322`. The proof uses
  `F3_Counts.verifier_bound` twice: `before` on (eval H P).2 and `after` on the enriched input. lean/F3T_Experiment.lean:15-26
  defines `original D P := bind P (verifier …)` and `recorded D build P := original D (compiled D build P)`, where `compiled`
  records `original D P` (:21-23). The recorded log is therefore prover Q, plus one model-verifier run inside compiled,
  plus a second run on the enriched input. That is Q + 1161 + 1161.
- lean/F3_Counts.lean:42-47 gives the single-run bound: "Checked complete-verifier envelope: 115 sampler + 477 batch0 + 6
  checkpoint + 563 batch1 = 1161". `F3_Model.verifier` (lean/F3_Model.lean:53-56) contains both batches and the checkpoint,
  so both transactions are already inside one 1161. The 2322 is two passes of the model verifier (the original run and the
  annotation compiler's re-run). It is not two transactions. F3T_Bounds.log_length and F3_Counts.verifier_bound are
  reachable.
- Other constants:
  - 1161 is the per-run issued-call envelope; `distinct_bound` gives firstReads ≤ Q+1161.
  - 1921 = 1018 + 903 is the account-run wrapper envelope (lean/ART_WrapperBudget.lean:14-21; lean/ARW_LocalBudget.lean
    `issued`, reachable).
  - 2965 = 1921 + 1044 audit reads (lean/Hiq_AccountAudit.lean:36, `Q0+Q1+1921+1044 = Q0+Q1+2965`).
  - `total` (lean/F3T_Numeric.lean:11-13) uses 34, 1161 and 2965. It does not use 2322.
- Claim draft (docs/research/100bit-spend-path-20261013/design/SOUNDNESS-CLAIM-DRAFT-20261108.md):
  - :405 "The issued-call log is at most Q+2322" is correct for the recorded/annotated log.
  - :427 "a_i must reproduce the verifier's digest calls of earlier attempts as its own queries, at most 2322 per attempt"
    (also :428 "2322 each") misdescribes the number. No theorem bounds an attempt's verifier calls by 2322. The per-attempt
    verifier-side envelopes in Lean are 1161 (model verifier) and 1921 (account-run wrappers). The second 1161 inside 2322 is a
    proof artefact of the recorded experiment, not a call the deployed verifier makes.
  - Because 2322 ≥ 1921 ≥ 1161, using V = 2322 over-counts, which is conservative: a larger Q_i gives a larger total(Q_i).
    In MAT_MultiAttempt, V is a free parameter (evidence/multi-attempt-20261108/MAT_MultiAttempt.lean:28, :244), and MAT is
    outside the release closure. Suggested fix: keep 2322 as a conservative envelope, but call it the two-pass recorded-log
    envelope, not "the verifier's digest calls". Alternatively, justify V = 1921 explicitly under H-MA2.

## 4. Recovery route: confirmed, with two refinements

- Reachable from both headline theorems: `AspisR1.OraclePortFrozenOrder.authenticated`,
  docs/research/100bit-spend-path-20261013/lean/OraclePortFrozenOrderSelectedRecovery.lean:49-74. Its premise is
  `accepted : (eval H (OraclePortShortCircuit.short (slotPrograms p q slots))).2 = true`, quantified over `kind < 3`. Its
  conclusion is `∀ pos, pos < 22 → recovered log frame p kind (index q kind pos) = some (OraclePortPackedChoiceC4.payload p kind pos)`.
  Its helpers `slots_accepted`, `slots_read`, `slotPrograms`, `verifySlot_frozen` and `recovery_at_index` are reachable.
- Not reachable (in the closure only): `OraclePortAllSelectedRecoveryC6.authenticated` (OraclePortAllSelectedRecoveryC6.lean:54).
  No constant of `OraclePortRecoveredAcceptanceC6` is reachable, including `accepted_checks` (OraclePortRecoveredAcceptanceC6.lean:38).
  - Refinement (a): eight C6 helpers are used through FrozenOrder.authenticated: `recovered`, `batchOf`, `batch_member`,
    `slot_member`, `leaf_fields`, `salt`, `tag` and `width`. So C6 is used at definition and lemma level, but its
    `authenticated` is not.
- Theorem-level path (all reachable): `AuS1_Context.authenticated` (lean/AuS1_Context.lean:15-36; call at :62-63) →
  `SdkC_Replay.recover_or_collision` (evidence/replay-dry8-20261026/RPz7_SdkC_Replay.lean:83-121; call at :118) →
  `OraclePortFrozenOrder.authenticated`.
  - Refinement (b): the slot program runs as a fixed canonical replay appended to the log, not in place on the original
    run. `replay p q := OraclePortFrozen2.batch p q slots` (:14-16: "Fixed canonical replay. The source is not changed or
    charged zero for it.") is bounded by `replay_bound ≤ 1040`. The conclusion is
    `hitsBad (… (Q+1040)) … (log ++ replay) ∨ ∀ pos < 22, recovered …`. This 1040 is the replay part of the 1044 audit reads in 2965.
  - Refinement (c): the headline call site fixes `kind = 2` and `j = 3`
    (AuS1_Context.lean:63, `… (Nat.le_refl _) 2 (by decide) frame 3 frameRead target`; the conclusion names
    `committedRoot parsed 2`). Source reading finds no other reachable caller of recover_or_collision or
    FrozenOrder.authenticated. The theorem is generic over the three trees, but the headline route instantiates only tree
    kind 2. Whether trees 0 and 1 are covered by another route is not established by this read.

target not yet established
