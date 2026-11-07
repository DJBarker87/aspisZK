# Owner decision: top statement form (conjunct 4 disjoined with the charged event)

Target not yet established. The decision is needed because the composed top for the actual code cannot conclude the adopted headline exactly. One conjunct (Outcome) holds only when the TX2 input satisfies Root0. Otherwise the top concludes the headline's own charged collision event in its place. That changes the adopted statement's shape (AGENTS.md §3). It also affects how the 100-bit per-attempt figure is derived. The 100-bit target itself is unchanged.

## Before (adopted, `AspisR1.RPx_Deployed.deployed`)

```
∀ {W A CoreError Tx} L sdk copy std allocator e1 e2 w1 w2 admission1 admission2
  missing indexError reservation native1 native2 hashv extraction sha256 H p1 syscall
  data1 data2 slot state1 state2 final1 final2 saved post1 post2 accepted1 accepted2
  root length prior words p t u actions game RuntimePersistence D a Q0 Q1 queries,
  C1 ∧ C2 ∧ C3 ∧ Outcome(…, bad := E_head) ∧ C5 ∧ C6 ∧ C7 ∧ C8 ∧ C9 ∧ C10 ∧ C11
```

## After (proposed top, `RSL.TFM.top_split` at the host)

```
∀ retained binders (L sdk copy std e1 e2 w1 w2 admission1 admission2 missing indexError
  reservation hashv sha256 H p1 syscall data1 data2 slot saved post1 post2 root length
  prior words p t u actions RuntimePersistence D a Q0 Q1),
  native1 := stage1_owned (sdk c), native2 := stage2_owned (sdk c)   -- instantiated
  A := Bool, allocator := abortIndicator, state1 = final1 = state2 = final2 := true  -- instantiated
  queries (at native1 := model), the actual TX1/TX2 entry runs returning Ok, the physical
  trace association, RuntimePersistence →
  C5num ∧ (C1 ∧ C2 ∧ C3 ∧ C5 ∧ C6 ∧ C7 ∧ C8 ∧ C9 ∧ C10 ∧ C11) ∧ (Outcome(…, bad := E_head) ∨ E_head)
```

Changes: `extraction`, `accepted1`, `accepted2` and `game` stop being hypotheses and become derived (extraction by `rfl` at the models). `native1/2` and the allocator binders are instantiated, not assumed. Conjunct 4 is weakened to `Outcome ∨ E_head`. The other ten conjuncts and the numeric clauses are unchanged and unconditional. The failure event, the work metric and the constants do not change.

## Why the exact form is not available

Outcome asserts the existence of the TX2 cut, its origin fact and the cohort reader success at that cut. These are facts about the model's TX2 run, and they are derivable for the actual code only on Root0 inputs (TFM_REPORT §1.2). The event appears only in Outcome's last conjunct, so it cannot stand in for the whole of Outcome.

## Consequence for the 100-bit per-attempt figure

The existing bound `failureModel ≤ total(Q) ≤ (Q+1)·2^-100` (Q ≤ maxQueries) already spends its one `accountLoss` term on a different recorded event (E_rec: the adversary's account run, adaptive selection). The top's event E_head is bounded separately, by the same amount (conjunct 5, `F3Y_AccountMass.Claims`). In the top form, E_head is what covers an actual TX2 acceptance that the model rejects. The deployed figure therefore becomes `total(Q) + accountLoss(Q)`. That still gives `(Q+1)·2^-100` for all Q ≤ 4925986828297653200597000880669438074876558273, about 2^151.8, which is two thirds of the current range. The Q = 0 margin stays positive. There is one further gap: E_head's bound is for a selection fixed in advance, while a real attacker chooses the TX2 accounts adaptively.

## Options

A. **Adopt the split form and charge E_head explicitly.** The deployed number becomes `total + accountLoss`, the range constant shrinks by a factor of 2/3, and a new Lean range lemma is needed. The adaptive-selection gap must still be closed, either by an adaptive-selection version of E_head or by B.
B. **Adopt the split form and re-target the case-split event to E_rec,** the event already charged inside `failureModel`. The number, the range and the margin are unchanged. This needs an NNC_ amendment: NMF′ must conclude E_rec at the actual run, which requires relating the deployed pair to the adversary's run. Feasibility is open.
C. **Keep the exact adopted form.** This requires Outcome at the actual code off Root0, which is not expected to hold (TCK §2.3). Not viable.

## Recommendation

Adopt the split form now, with B as the target and A as the fallback. B keeps every adopted number. A is honest, within 100 bits per attempt, and costs only range, but it leaves the adaptive-selection gap to close. In either case, report "target not yet established" until the chosen event is proved charged. The allocator instantiation (A := Bool, abort indicator) is a lead decision recorded in TFM_REPORT §2. It adds no trust and does not restrict the attacker, and it is listed here only for visibility.
