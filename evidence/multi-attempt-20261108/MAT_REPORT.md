# MAT_: repeated, separately submitted spend attempts (stand-in level)

Target not yet established. This adds a compiled stand-in theorem for the
campaign case that SOUNDNESS-CLAIM-DRAFT-20261108 section 3.5 left as an
unchecked union-bound sketch. It does not change the per-attempt number, the
contract, or the release target.

## 1. Statement

`RSL.MAT.campaign_charge` (MAT_MultiAttempt.lean). Fix one oracle space
`X.Oracle` and one expectation `Ex` (TASB.Expect) over it. For k attempts,
attempt i is given by a reduction adversary `fxOf i : X.Fixed` and a world map
`wOf i : X.Oracle → X.World`, with the per-attempt host inputs `r i`, `m i`,
`budget i : E m_i + E 1_{E_rec at fxOf i} ≤ T i`. Then

    Ex.E (fun H => ind (∃ i, i < k ∧ Forged I hb X (fxOf i) (wOf i H) H)) ≤ Σ_{i<k} T i

and, keeping the extractor-failure mass,
`Ex.E (fun H => Σ_{i<k} max (r i H) 1_{Forged i H}) ≤ Σ_{i<k} T i`.
`Forged … H` is exactly the event inside `deployed_charge`: the deployed pair
of attempt i is a successful actual run (`Runs`) and `OutcomeRec` fails.

`RSL.MAT.campaign_bound` composes this with `F3U_Range.per_attempt` (a
hypothesis `perAttempt` here) and the reduction cost:

    Pr_H[some attempt i < k forges] ≤ k · (c·(qTot + V·(k−1)) + 1) · 2^-100
    provided c·(qTot + V·(k−1)) ≤ maxQueries,

where qTot bounds the campaign adversary's own issued queries over the whole
campaign, V = 2322 is the per-attempt verifier digest-call envelope (claim
draft 3.3), and c is the phase factor (section 3). The sharper form before the
linearisation is Σ_{i<k} total(Q_i), Q_i the issued-call count of attempt i's
reduction adversary.

Compiled: exit 0, 0.56 s, 436 MB peak RSS, 0 swaps (MAT_COMPILE.tsv).
`#print axioms`: propext, Classical.choice, Quot.sound only
(MAT_AXIOMS_OUTPUT.txt). No sorry, no axiom declaration, no Realizes premise.

## 2. How queries are counted, and which per-attempt bound applies

Attempt i is charged at total(Q_i), where Q_i is the issued-call length of the
reduction adversary a_i that simulates the campaign up to attempt i:

- every query the campaign adversary issued before attempt i's pair is fixed,
  including all queries made during earlier attempts (cumulative, not fresh);
- a re-issue of every earlier attempt's verifier digest calls (≤ V each), so
  that a_i can reproduce what the adversary observed;
- with c = 2, the second phase's recomputation of the first phase.

The bound is therefore Σ_i total(Q_i) with Q_i cumulative, not Σ_i total(q_i)
with Σ q_i ≤ Q_total over fresh queries. The fresh-query form would be a
per-attempt bound conditioned on the history. `deployed_charge` does not state
one, and none holds in general: queries made during attempt 1 may already have
found the transcript start that attempt 2 then submits with no new queries, so
attempt 2's conditional failure probability given that history can be 1.
The union bound uses only the unconditional mean of each attempt's loss over
all H, which is what `deployed_charge` provides. No independence across
attempts is assumed.

A tighter joint bound is plausible: the start charge and both collision terms
are events on one global query log, so a direct single-experiment analysis
would give about total(Q_total) plus k times the verifier constants, rather
than about k·total(Q_total). That needs a new host argument on the merged log
(E_rec is defined on each reduction adversary's own account run, so the
per-attempt events are not monotone in a shared log at stand-in level). It is
not proved and not claimed.

## 3. Phase factor c

`SCE_Experiment.Adversary` (lean/SCE_Experiment.lean line 13) is
`first : Program Bytes State (FirstInputs A)` and
`second : FirstInputs A → Vec U8 → Heap … → A → Program …`. The second phase
receives its own first output and the chain values saved/post1/final1, but no
private state. A reduction adversary must therefore recompute its campaign
simulation in the second phase, and `issued` counts both phases, duplicates
included. Hence c = 2 for the current adversary type. c = 1 would need a host
argument that the state can be carried without changing the submitted bytes.
The claim draft's sketch Σ total(Q_adv + (i−1)·2322) omits this factor; it
should read Σ total(Q_i) with Q_i ≤ 2·(Q_adv,≤i + 2322·(i−1)) (1-indexed), or
c must be shown to be 1.

## 4. Does the existing per-attempt theorem already support this?

Yes, with no new per-attempt lemma. `deployed_charge` quantifies `fx`
(carrying the adversary) and `wOf` universally, takes `QueriesF fx` as a
parameter, has no Realizes premise (`realizes_by_construction`), and averages
over all H with no conditioning. `campaign_charge` instantiates it k times on
one `X` and one `Ex`, with a different `fxOf i` and `wOf i` per attempt, and
adds only the generic `union_charge`. Chain state left by earlier attempts is
covered because `wOf i` is an arbitrary function of H.

What is new and not discharged at stand-in level (host obligations):

- **H-MA1** construction of a_i : SCE_Experiment.Adversary from a campaign
  adversary, with `(eval H a_i.first).2` and `(eval H (a_i.second …)).2` equal
  to attempt i's submitted inputs at every H.
- **H-MA2** its cost, `cost : Qof (fxOf i) ≤ c·(qAdv i + V·i)` (0-indexed),
  with Qof fx = Q0+Q1 and `QueriesF (fxOf i)` at that budget.
- **H-MA3** environment condition: whatever the campaign adversary sees
  between attempts is a function of H and of oracle-free data fixed before H,
  so a_i can hard-wire it or recompute it with charged queries. This is the
  same restriction the per-attempt game already places on one attempt (the
  adversary is an oracle program; World binders vary with H but the
  adversary's outputs do not read them), extended across attempts. It is not
  a new restriction on the attacker's query budget.
- No host lemma for monotonicity of F3T_Numeric.total was found; the numeric
  form avoids needing one by applying `per_attempt` at each Q_i.

## 5. Owner

No owner decision is needed for the stand-in. Accepting the campaign wording
for publication is within the lead's delegation (2026-10-28); the per-attempt
target and metric are unchanged, and nothing here sets a single-experiment
bound to 1 to infer campaign cost. If the lead reads H-MA3 as narrowing the
adversary beyond the per-attempt game, that is a contract-scope question for
the owner.

## 6. Reproduction

From evidence/rowspec-lead-20261107: `sh rsl_compile.sh` on RSL_Base ..
RSL_TX1_330 (order in RSL_COMPILE_FINAL.tsv), then staged
`lake env lean -o .lake/build/lib/lean/<m>.olean .lake/stage/<m>.lean` for
TCK_WeakRoot0, TAS_Interfaces, TAS_Top, TFM_TopExact, EVB_EventB, TAS_TopB,
then `sh ../multi-attempt-20261108/mat_compile.sh`. Toolchain
leanprover/lean4:v4.31.0. All upstream files were compiled unchanged from
research at the revision in MAT_COMPILE.tsv.
