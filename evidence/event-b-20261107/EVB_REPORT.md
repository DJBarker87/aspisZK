# EVB: feasibility of option B and the cost of option A's adaptive gap

Target not yet established. This report decides the question left open in TFM_OWNER_MEMO (options A and B). It closes no row and adds no trust. It proposes one change to the top statement, a new hypothesis, which needs the owner's approval. Base: `research` at 1422835d3c4. Headline sources were read from `evidence/replay-deployed2-20261027/RPx_Deployed.lean` and from `lean/` (`FJp_Mass`, `ARX_LocalCharge`, `ART_PartialAccount`, `ARQ_Observer`, `Hiq_ByteSelection`, `Hiq_RecordedJoint`, `F3X_Account`, `F3Y_AccountMass`, `F3T_AccountCharge`, `P2P_Charge`, `P2P_NativeSelection`, `SCE_Experiment`, `ARW_Induced`, `GExq_AccountExperiment`, `CPH_Game`, `ARS_Coverage`, `ARU_Support`, `ARU_SourceResults`, `ARV_FirstPartial`, `ARW_AdmittedQueries`, `ARW_LocalBudget`, `ARX_SourceAlternative`, `ARU_Selector`, `FJv_DRelease`, `ARV_Constant`). The NNC_ fold was read from `codex/cx-root0-weak-20261107` at a1fbcff5c83 (`NNC_BindingRoot.lean`, `NNC_CaseSplit.lean`).

## 0. Verdict

- **B is provable, but only after the top gains one new hypothesis, `Realizes`.** `Realizes` says that the deployed pair is the adversary's own run at the actual oracle H. No headline binder supplies it, and none lets it be proved, because `a` and the deployed pair are quantified independently. With `Realizes`, everything else is TX1-only re-use of existing lemmas. There is no new mathematics and no new trust. The size is about 400–500 lines of host Lean in roughly 10–15 focused scopes.
- `Realizes` does not restrict the attacker. It is satisfiable for every deployed pair (`ARV_Constant.adversary`, zero queries). It also makes the adaptive choice of the pair a charged part of `a`, so B closes the adaptive-selection gap by construction. The per-attempt number stays `total(Q)` and the range stays `maxQueries` ≈ 2^152.37. E_rec is charged once (`no_second_charge`).
- **Option A's adaptive gap cannot be closed by any lemma about E_head alone.** If the pair may be an arbitrary function of H, the adaptive probability of E_head can be 1. Bounding it requires the pair to be the output of a query-bounded program, which is the `Realizes` relation again. The account-mass lemma that would then apply already exists (`F3T_AccountCharge.bound` with an output-dependent selector), and applying it gives E_rec or a twin of it. "A plus adaptive closure" therefore costs everything B costs, plus a second `accountLoss` charge, a range of ≈ 2^151.79 and a new Lean range lemma.
- **Recommendation:** adopt the split form with full B (both the case-split event and Outcome's inner `bad` re-targeted to E_rec), plus the new hypothesis `Realizes`. Drop A as a fallback. A is strictly dominated, because without `Realizes` its 2^151.8 figure is valid only for a pair fixed before H.

## 1. The relation B needs

### 1.1 The two events (exact)

E_rec, from `FJp_Mass.bounded` (the event already charged inside `failureModel`):

```
let cfg := FIp_Install.configuration err c r
let source := ART_PartialAccount.account cfg hashv copy allocator CPH_Program.verifier a
let capped := ARX_LocalCharge.bounded source (Q0+Q1)
let recorder := Hiq_RecordedJoint.program capped ARQ_Observer.project (ARQ_Observer.select cfg CPH_Program.verifier)
let event := BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965)
-- E_rec(H) := event (eval H recorder)
```

E_head, from `RPx_Deployed.deployed` (the top's event under A):

```
let P := ARW_Induced.program native1 copy allocator CPH_Program.verifier a
let select := fun _ => P2P_NativeSelection.pair (DrvC_Installation.sdk cfg) CPH_Program.verifier e1 e2 data2 slot
-- E_head(H) := BinRawByteCollisionTargets.event … (Q0+Q1+2965)
--   (eval H (Hiq_RecordedJoint.program (F3X_Account.program cfg hashv P) F3X_Projection.project select))
```

The adversary and its run:

```
structure SCE_Experiment.Adversary (A : Type) where
  first : Program Bytes State (FirstInputs A)
  second : FirstInputs A → alloc.vec.Vec U8 → Heap (Nat → Record) → A → Program Bytes State (SecondInputs A)

def ART_PartialAccount.account : Program Bytes State (Outcome A) :=
  bind a.first fun i =>
    bind (wrapper hashv (firstSyntax c hashv copy allocator id i)) fun reply =>
      match reply with
      | .ok (.Ok (saved,post,final)) =>
        bind (a.second i saved post final) fun j =>
          bind (wrapper hashv (secondSyntax c hashv allocator id j)) fun out => .done (i,reply,some (j,out))
      | _ => .done (i,reply,none)

def Hiq_ByteSelection.select ops id (out : Outcome A) :=
  (⟨(account ops out.1.entry.first 0#usize).drop 688, account ops out.1.entry.first 1#usize⟩,
   match out.2.2 with
   | none => ⟨[],[]⟩
   | some (next,_) => ⟨(account ops (next.entry.second secondSizes) 0#usize).drop 688,
       public2 ops id (next.entry.second secondSizes) next.data next.slot⟩)

def P2P_NativeSelection.pair ops id e1 e2 data2 slot :=
  (⟨(Hiq_ByteSelection.account ops e1.first 0#usize).drop 688, Hiq_ByteSelection.account ops e1.first 1#usize⟩,
   ⟨(Hiq_ByteSelection.account ops (e2.second secondSizes) 0#usize).drop 688,
    Hiq_ByteSelection.public2 ops id (e2.second secondSizes) data2 slot⟩)
```

The charging lemma is generic in the source, the projection and the selector:

```
theorem P2P_Charge.binding_or_collision (source) (project) (select) (Q)
    (budget : ∀ H, firstReads emptyTable (eval H source).1 ≤ Q+1921) (H) :
    BinRawByteCollisionTargets.event iv (Q+2965) (eval H (Hiq_RecordedJoint.program source project select)) ∨
    R9PoolRuntimeBinding.P2Prime H (select (eval H source).2).1 (select (eval H source).2).2
```

### 1.2 Where the selector enters the NNC_ proof

`NNC_BindingRoot.root0_or_existing_collision` is already generic in `source` and `project`. Its selector is the constant `fun _ => pair ops id e1 e2 data2 slot`. The proof uses the selector at exactly one point: on the binding branch, `P2Prime H (select (eval H source).2)…` is read as P2Prime at the pair's bytes, and then `on_cuts` and `root0_of_binding` give Root0. For E_head that reading is `rfl`. For E_rec it needs

```
SelectsPair :≡ ARQ_Observer.select cfg CPH_Program.verifier (eval H capped).2
               = P2P_NativeSelection.pair (DrvC_Installation.sdk cfg) CPH_Program.verifier e1 e2 data2 slot
```

`EVB_EventB.core` checks this factorisation (the selector is used only through `selects`), and `core_head` shows that the existing NMF′ is the `rfl` instance. The production `failureModel` proof already follows the E_rec pattern: `ARX_SourceAlternative.accepted` applies `ARX_LocalCharge.binding` with the ARQ selector and rewrites by `ARU_Selector.selected`. It does this under the support record `ARU_Support.At`, which includes `accepted2`.

### 1.3 The relation, and why SelectsPair reduces to it

`Sel.select_realized` (compiled, a verbatim transcription) shows that `select (i, r, some (j, o)) = pair i.entry j.entry j.data j.slot` holds by `rfl`. `Sel.select_unreached` shows that the TX2 half is `⟨[],[]⟩` when the adversary's run never reaches TX2. SelectsPair therefore needs exactly the following relation, with `i := ⟨e1, data1, state1⟩`:

```
Realizes :≡ (eval H a.first).2 = i ∧
            (eval H (a.second i saved post1 final1)).2 = ⟨e2, data2, slot, state2⟩
```

The relation also needs the adversary's run to reach TX2 with reply `ok (.Ok (saved, post1, final1))`, and its log to fit the cap. Both follow from facts that are already in scope and are Root0-free:

- First reply. `ART_WrapperExact.execution`, with Agrees from `p1` (`sha256 = H`) and `syscall` (`hashv parts = ok d → decodeState d = sha256 (flatten parts)`), followed by `ARU_WrapperSource.first` from extraction (A0) and accepted1 at the model (A3). These are the TX1 halves of `ARU_SourceResults.accepted` and `ARV_FirstPartial.accepted`, with the `At` record replaced by `Realizes`.
- Budget. With equal first replies, `ARW_Induced.issued` has length `ART_AdversaryWork.work` (as in `ARW_AdmittedQueries.admitted`, which uses only `n.entry.accepted1`). Then `queries` and `ARW_LocalBudget.issued` give a log of at most Q0+Q1+1921, and `ARX_LocalCharge.exact` removes the cap.

Realizes is the TX1 half of `ARS_Coverage.SupportedEntry` with `accepted2` dropped. `SupportedEntry` is the record through which `failureModel`'s own runtime identifies the entries: its fields `admission1`, `accepted1` and `game` use `(eval H a.first).2.entry` and `(eval H (a.second (eval H a.first).2 saved post1 final1)).2.entry` as e1 and e2. The headline's separately quantified `e1 e2 data1 data2 slot` are a second copy that is not connected to it. Realizes reconnects the two.

### 1.4 The headline binders do not supply Realizes, and do not let it be proved

`a` appears in `RPx_Deployed.deployed` only in

```
(queries : ∀ H : Bytes → State, (ARW_Induced.issued native1 copy allocator CPH_Program.verifier a H).length ≤ Q0+Q1)
```

and in the let-bound `P` and `runtime`. The other candidate binders do not mention `a` or the adversary's run:

```
game : CPH_Game.DeployedPairExecution p t u e1 e2 saved actions native1 native2 copy allocator CPH_Program.verifier
  -- consecutive : p.next t u ∧ e1 = entry p t ∧ e2 = entry p u
  -- checkpoint : ((p.layout t).handles 2).1 = ((p.layout u).handles 6).1 ∧ CPS_PhysicalKey.key e1 2 = CPS_PhysicalKey.key e2 6 ∧ …
  -- parent : success p t = true
  -- recorded : (p.copied t = saved ∧ p.actions t = sourceActions ∧ CPG_RuntimeTrace.Executes …) ∧ CPG_RuntimeTrace.Executes …
RuntimePersistence : CPR_DataPersistence.TwoTransactionLaw (CPG_Projection.adjacent p) (CPG_Projection.ordinary p …)
  (CPG_Projection.before p) (CPG_Projection.tentative p) (CPG_Projection.success p) (CPG_Projection.loaded p)
p : CPG_Projection.Observations Tx A;  t u : Tx;  actions : List (CPP_BankState.Action A)
```

So `game`, `RuntimePersistence`, `p`, `t`, `u` and `actions` tie `e1`/`e2` to the physical bank lineage, never to `a`. `queries` only bounds the length of `a`'s issued list. Counterexample to deriving "actual TX2 accepted ∧ ¬Root0 ⇒ E_rec" from the binders: take `a := ARV_Constant.adversary i0 j0` for a fixed `i0` that the model TX1 rejects. It issues no queries, so `queries` holds with Q0 = Q1 = 0, and its account run has TX2 selection `⟨[],[]⟩`. Take H that collides on the deployed pair's P2Prime reads but not on `a`'s fixed audit reads. Then E_rec(a, H) is false. Root0 at the deployed pair is exactly what that collision defeats, and NNC_ itself needs its event branch for this case. This is an argument, not Lean-checked. It shows the implication is not a consequence of the binders.

### 1.5 Realizes is a statement change, but not an attacker restriction

- **Satisfiable and lossless per world.** For any deployed pair, `ARV_Constant.adversary ⟨e1,data1,state1⟩ ⟨e2,data2,slot,state2⟩` realizes it at every H with zero issued queries. So every per-world instance of the old conclusion is still covered, by some `a`.
- **Correct probability law.** The bound `failureModel` is a function of `a`, while `Concl` is per world. Without Realizes, nothing ties the pair at H to the `a` being charged (TFM §1.4.6). With Realizes, `Pr_H[¬Concl]` is taken over the pair that `a` actually produces at H. An attacker that picks the pair after querying H is some `a` whose queries are counted in Q0+Q1 through `queries`. This is the ROM work metric already in the contract. No grinding credit is used, and repeated attempts are accounted for as before, one `a` per attempt.
- **Rejected alternative.** One could instantiate `a := ARV_Constant.adversary …` at the top, the way native1/2 and the allocator were instantiated. That would make Realizes hold by `rfl`, but the numeric claim would then cover only pairs fixed before H. That is a silent restriction of the adversary (AGENTS.md §2) and must not be done.
- **Owner item.** Realizes adds a hypothesis that links two previously independent binder groups, so it changes the adopted statement's quantifier structure (§3). Before/after are given in §4.

## 2. Option B: what NMF′ must state, and the work

### 2.1 Compiled stand-in (`EVB_EventB.lean`)

This is in TAS/TFM stand-in form. `RecSig` carries the host stand-ins `Realizes`, `EventRec` (E_rec, which takes no `First`/`Second` argument because `ART_PartialAccount.account` runs the source syntax, not native1/2) and `SelectsPair`. The deliverables are:

```
structure RecSelect (R : RecSig S) where
  selects : ∀ c, S.Exhibited c → S.Extraction c (S.model1 c) (S.model2 c) →
    S.Accepted1 c (S.model1 c) → S.Queries c (S.model1 c) → R.Realizes c → R.SelectsPair c

structure NNC_NMFPrimeB (g : NNC_G1a S L V0 VL I) (R : RecSig S) where
  root0_or_rec : ∀ c, S.Exhibited c →
    (∀ a s env, TX2_213.Ref L D (lib V0 (fun _ _ => True) g.w) (TX1_344.asStage1 VL P C) a s env (I.entry a s env)) →
    (∃ s', (I.entry (S.args2 c) (S.state2 c) (S.env2 c)).exit = .ret (.ok (), s')) →
    S.Accepted1 c (S.model1 c) → S.Game c (S.model1 c) (S.model2 c) →
    S.Extraction c (S.model1 c) (S.model2 c) → S.Queries c (S.model1 c) →
    R.SelectsPair c → S.Root0Native c ∨ R.EventRec c

structure HeadlineB (S : Sig) (R : RecSig S) where
  OutcomeRec : S.Ctx → S.First → S.Second → Prop          -- FJv_DResult.Outcome … (bad := E_rec)
  outcomeRec : ∀ c n1 n2, S.Extraction c n1 n2 → S.Accepted1 c n1 → S.Accepted2 c n2 →
    S.Game c n1 n2 → S.Queries c n1 → R.SelectsPair c → OutcomeRec c n1 n2
```

`top_splitB_full` has TFM `top_split`'s hypotheses with `nmf`/`cs` replaced by `R`, `rs`, `hb` and `nmfB`, plus `realizes : R.Realizes c`. It concludes

```
S.Bound c m1 m2 ∧ sp.Rest c m1 m2 ∧ (hb.OutcomeRec c m1 m2 ∨ R.EventRec c)
```

`top_splitB` is the variant that re-targets only the case-split event and keeps the adopted Outcome. It is not sufficient on its own, because the adopted Outcome's inner `bad` is E_head and keeps the fixed-selection caveat on the Root0 arm. That inner event is produced in one place, `FJv_DRelease.remove` line 90 (`P2P_Charge.binding_or_collision account project (fun _ => pair …)`), and `remove` is already generic in `account`/`project`. `HeadlineB.outcomeRec` is that one line generalised as in §1.2, together with a copy of `FJv_DNativeAccepted.accepted` instantiated at the capped account run.

`no_second_charge` (over `Rat`) states the per-world fact `max r (1_{¬Outcome}) ≤ m + 1_{E_rec}`, given `r ≤ m + 1_{E_rec}` (the `each` of `FJp_Mass.bounded`), `0 ≤ m` and `¬Outcome → E_rec`. Averaging it as `F3U_Averaging.charge` does gives a deployed per-attempt failure of at most `total(Q0+Q1)`, with E_rec charged once. That averaging step is a host restatement and is not compiled here.

Compile record (EVB_COMPILE.tsv): `lake env lean` on the single file against locally rebuilt RSL_ (20 modules, each ≤ 0.70 GB), TCK_, TAS_ and TFM_ oleans. Exit 0, wall 0.30 s, peak RSS 432,095,232 bytes, swaps 0, sha256 43645d9f40aa546c8b3b67a9c543f135ba4882146417bb3ca2f32acc00bce74d, Lean 4.31.0. `#print axioms` (EVB_AXIOMS_OUTPUT.txt): `core`, `core_head`, `Sel.select_realized` and `Sel.select_unreached` use no axioms. `top_splitB`, `top_splitB_full` and `no_second_charge` use [propext, Classical.choice, Quot.sound], the same as TFM `top_split`. There is no sorry, no axiom declaration and no Root0 hypothesis.

### 2.2 Host statements (exact, not compiled here)

NMF′-B core (the NNC_ amendment) is `NNC_BindingRoot.root0_or_existing_collision` with the selector generalised:

```
theorem root0_or_rec_collision {A Ambient X : Type} (source : Program Bytes State A)
 (project : A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
 (select : A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs)
 (Q : Nat) (budget : ∀ H, firstReads emptyTable (eval H source).1 ≤ Q+1921)
 (H : Bytes → State) (ops) (id) (e1 e2) (data2) (slot) (saved) (f : FirstCut) (s : SecondCut)
 (cuts …) (origin …) (writerRoot …) (persisted …) (writerHeader …) (d) (hash) (world) (domain …) (oracle …)
 (records …) (events …) (native …)                                   -- all unchanged from NNC_
 (selects : select (eval H source).2 = P2P_NativeSelection.pair ops id e1 e2 data2 slot) :
 (NLP_InputDomain.Root0 s.checkpoint s.proof ∧ NLT_CompleteRoot.RowSpec H d s.pub s.proof s.checkpoint hash) ∨
 BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+2965)
  (eval H (Hiq_RecordedJoint.program source project select))
```

It is instantiated at `source := ARX_LocalCharge.bounded (ART_PartialAccount.account cfg hashv copy allocator CPH_Program.verifier a) (Q0+Q1)`, `project := ARQ_Observer.project`, `select := ARQ_Observer.select cfg CPH_Program.verifier`, `Q := Q0+Q1` and `budget := fun K => (VerifierCallBudget.firstReads_le_length _ _).trans (ARX_LocalCharge.budget _ _ K)`, exactly as in `FJp_Mass.bounded`. The event is then literally E_rec.

RecSelect (host):

```
theorem selects (extraction : S2W_DigestExtraction.AeneasExtraction (DrvC_Installation.sdk cfg) native1 native2 hashv)
  (p1 : S2W_ExtractionBoundary.P1 sha256 H) (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
  (accepted1 : S2W_D189Wrappers.first native1 copy allocator e1 CPH_Program.verifier data1 state1 = ok (.Ok (saved,post1,final1)))
  (queries : ∀ H, (ARW_Induced.issued native1 copy allocator CPH_Program.verifier a H).length ≤ Q0+Q1)
  (r1 : (eval H a.first).2 = ⟨e1, data1, state1⟩)
  (r2 : (eval H (a.second ⟨e1, data1, state1⟩ saved post1 final1)).2 = ⟨e2, data2, slot, state2⟩) :
  ARQ_Observer.select cfg CPH_Program.verifier
    (eval H (ARX_LocalCharge.bounded (ART_PartialAccount.account cfg hashv copy allocator CPH_Program.verifier a) (Q0+Q1))).2 =
  P2P_NativeSelection.pair (DrvC_Installation.sdk cfg) CPH_Program.verifier e1 e2 data2 slot
```

### 2.3 Work estimate (B)

| Item | Owner | Size | Notes |
|---|---|---|---|
| Generalise the NNC_ fold selector (`from_headers`, `root0_or_existing_collision`, `NNC_NMFPrime.assemble`) | NNC_ | 40–60 lines, 1–3 scopes | the proof is unchanged apart from one `rw [selects]` |
| `RecSelect.selects` | new job | 120–200 lines, 4–8 scopes | TX1-only copies of `ARU_SourceResults.accepted`.1, `ARV_FirstPartial.accepted` and `ARW_AdmittedQueries.admitted`; Agrees from p1/syscall; `ARX_LocalCharge.exact`; final `rfl` |
| `FJv_DRelease.remove'` and the `FJv_DNativeAccepted` copy (inner `bad` := E_rec) | new job | about 60 + 140 lines, 2–4 scopes | heavy imports, so compile on the build host under the cgroup caps |
| Top: split form plus `realizes`, and the averaged deployed figure (`max r _` version of `F3U_Averaging.charge`) | lead assembly | about 60–100 lines | the stand-in is already compiled |

The total is about 400–500 lines in about 10–15 focused scopes. It needs no new mathematics, no new trust and no change to any number. B inherits whatever NNC_'s NMF′ still has open (its handoff lists the selected native-packet extraction, NativeRep and the readerHeader representation). B adds nothing to that list.

## 3. Option A: the adaptive-selection bound for E_head

**What is needed.** A bound on `Pr_H[E_head(pair(H), H)]` when the pair `(e1, e2, data2, slot)` depends on H.

**It is not available without a computational model of the selection.** `BinRawByteCollisionTargets.event` is `hitsBad (AllAddressCollision.bad iv pred Q) emptyTable v.1`, a collision among the recorded reads, and those include the audit reads of the selected pair (P2P_Charge: "1921+1040+4"). If the pair is an arbitrary function of H, then by pigeonhole on fixed-length inputs (proof suffix 57607 bytes against a 32-byte state) every H has a pair whose audit reads collide. The supremum over adaptive selections is therefore 1. A union bound over all pairs is useless at that domain size. This is an argument, not Lean-checked.

**Existing versus new.** The account-mass family already contains the adaptive lemma for selections that are outputs of a program. `F3T_AccountCharge.bound source project select Q budget` holds for any `select : X → Inputs × Inputs` applied to the source's own output, and `FJp_Mass` uses it with the output-dependent `ARQ_Observer.select`. `F3Y_AccountMass.Claims` is that lemma at E_head's program with a constant selector. Closing A's gap means (i) making the pair the output of some query-bounded program `a'`, which is the `Realizes` relation for `a'`, and (ii) applying `F3T_AccountCharge.bound` to that program. Taking `a' := a` gives back E_rec, the event already charged, and that is B. Taking a different `a'` gives a second event charged separately. So no new probability mathematics is needed, but A's adaptive closure needs all of B's relation work (§2.3) plus a second `accountLoss` and a new Lean range lemma. Its size is B's 400–500 lines plus about 50 lines for the range lemma (`gap'` with `2·accountLoss`, edges at the new constant, the Q = 0 margin).

**Range figure, checked** (EVB_range.py, exact rationals, output in EVB_RANGE_OUTPUT.txt):
- `total(Q) ≤ (Q+1)·2^-100` exactly for Q ≤ 7388980242446479800895501321004157112314840375 = `F3U_RangeEdges.maxQueries` (≈ 2^152.372). This reproduces the Lean constant.
- `total(Q) + accountLoss(Q) ≤ (Q+1)·2^-100` exactly for Q ≤ 4925986828297653200597000880669438074876558273 (≈ 2^151.787). The ratio is exactly 2/3, as stated in TFM.
- At Q = 0, `2^-100 − total(0) − accountLoss(0) ≈ 0.999996·2^-108 > 0`.

The 2^151.8 figure is correct as arithmetic. Without `Realizes`, though, it holds only for a pair fixed before H. It is not an adaptive per-attempt bound and must not be reported as one.

## 4. Statement change for the owner

Before (TFM proposal, option A or B):

```
∀ retained binders (… e1 e2 … data1 data2 slot … saved post1 post2 … a Q0 Q1), queries, …, RuntimePersistence →
  C5num ∧ Rest ∧ (Outcome(…, bad := E_head) ∨ E_head)
```

After (full B):

```
∀ the same binders, queries, …, RuntimePersistence,
  (realizes : (eval H a.first).2 = ⟨e1, data1, state1⟩ ∧
              (eval H (a.second ⟨e1, data1, state1⟩ saved post1 final1)).2 = ⟨e2, data2, slot, state2⟩) →
  C5num ∧ Rest ∧ (Outcome(…, bad := E_rec) ∨ E_rec)
```

What changes: there is one added hypothesis linking `a` to the deployed pair at H, and both occurrences of E_head in conjunct 4 become E_rec. Quantifiers, carriers, the failure event's form (the same `BinRawByteCollisionTargets.event` at `Q0+Q1+2965`), the work metric, the constants, `C5num` and the other ten conjuncts are unchanged. `F3Y_AccountMass.Claims` for E_head stays in conjunct 5a; it remains true but is no longer the charge that covers conjunct 4. The deployed per-attempt figure is `total(Q0+Q1) ≤ (Q0+Q1+1)·2^-100` for `Q0+Q1 ≤ maxQueries`, as adopted. The added premise is satisfiable for every pair, by a constant adversary, and it does not contain the conclusion.

## 5. Handoff

- **Established:** `RSL.EVB.core`, `core_head`, `Sel.select_realized`, `Sel.select_unreached`, `top_splitB`, `top_splitB_full` and `no_second_charge` (compiled, TAS stand-in form). The exact relation B needs, and the finding that no headline binder supplies it (§1.4). The range figures (exact rationals, not Lean-checked).
- **Discharged:** none. **Retained:** everything TFM retains. **Added (proposed):** the top hypothesis `realizes` (owner decision) and the host obligations `RecSelect.selects`, `NNC_NMFPrimeB.root0_or_rec` and `HeadlineB.outcomeRec`, all re-use of existing lemmas with no trust. **Changed:** none until the owner decides.
- **Validation run:** local rebuild of RSL_ (20 modules) and of the TCK_/TAS_/TFM_ chain, then the EVB_ single file. There was no package, host or manifest replay. Host statements in §2.2 are not compiled. The pigeonhole argument in §3 and the counterexample in §1.4 are not Lean-checked.
- **Next deliverable:** the owner's decision on `Realizes` and full B. On approval: an NNC_ amendment (selector generalisation), a RecSelect job and a remove′/DNativeAccepted′ job, then the lead assembles the split-B top.
