# The one-transaction game and the step from acceptance to checks

Status, 2026-11-11. Scoping and statements only; no proof and no Lean compiled
for this note. "R1" is the two-transaction verifier and its Lean development
(the L187 closure, read from the flat copy of its 13,552 sources). "Aspis" is
the one-transaction verifier: `stage2_owned` under `future-one-tx`
(programs/r1-cost-probe/src/r1_pool_adapter_owned.rs:417-454) calling
`verify_summed_format` (crates/aspis-r1-cost-probe/src/fused.rs:812), read at
the branch head (01f5312ca0e). No security figure is quoted for Aspis and none
of R1's is restated. The release target is unchanged and not yet established.

## 0. What does not carry over, and what cannot be established here

1. **R1's game is two-phase in its types, not only in its hypotheses.** The
   adversary type (`SCE_Experiment.Adversary`), the account program
   (`GExq_AccountExperiment.program`), the query count (`ARW_Induced.issued`),
   `Runs`, `GameFrame` and the retained runtime conjunction all name the second
   phase. Aspis needs its own copies of each. Their definitions can be written
   now; instantiating them needs an extracted model of the Aspis entry (the
   one-transaction `stage2_owned`), which does not exist.
2. **The account term (2,965) has no derivation for Aspis.** Of its three parts,
   one (the four audit reads behind `R9PoolRuntimeBinding.P2Prime`, which says
   that the second transaction read the buffers the first transaction digested)
   exists only because there are two transactions. The other two (the account
   run's own issued calls and the replay of the Merkle slots) have one-transaction
   analogues only if the Aspis headline keeps R1's split-B outcome conjunct.
   That is a decision about the failure event (section 5, D2), not a proof
   question. Paper counts are in section 2.3.
3. **R1's 2,322 does not come from the two transactions.** In the Lean it is
   `OraclePortStoredExperimentC4.recorded_length`/`OraclePortFrozen2.log_length`:
   Q plus two runs of the model verifier (the original run and the annotation
   compiler's re-run), each at most 1,161. SOUNDNESS-ARGUMENT.md section 6.4
   attributes it to the two-transaction account run. That attribution is wrong
   for the Lean, so the correction is recorded here and that file is not edited.
4. **Accepted ⇒ checks is model-level in R1, and so is its Aspis counterpart.**
   R1's chain from acceptance of the model decision to `Checks`, including the
   three-tree commitment recovery, lies inside the closure of
   `Frozen2StartChargeProbability.failure_bound`. It is a theorem about the model
   verifier in R1's Bin commitment model. The source refinement is a separate
   hypothesis (`AcceptedRunJoin`). ASPIS-INSTANCE-PLAN.md item 15 placed this
   step in "the source/commitment layer". Its commitment part is in fact model
   level and can be written now against R1's objects. Only the Rust-to-model join
   is source refinement.
5. **Correction to a reference in the pair-binding result.** R1's bound reaches
   the three-tree recovery through the frozen-order chain:
   `Frozen2StartChargeClean.accepted_facts` ← `OraclePortFrozen2Consumer.fibre_checks`
   ← `OraclePortFrozen2C6.checked_acceptance` ← `OraclePortFrozen2CanonicalChecks.accepted_checks`
   ← `OraclePortFrozen2ActualChecks.accepted_checks` ← `OraclePortFrozenOrderChecks.accepted_checks`
   ← `OraclePortFrozenOrder.authenticated` (OraclePortFrozenOrderSelectedRecovery.lean:49)
   ← `OraclePortFrozenOrder.recovery_at_index` (OraclePortFrozenOrderCutRecovery.lean).
   That chain does not go through `OraclePortAllSelectedRecoveryC6.authenticated` or
   `OraclePortRecoveredAcceptanceC6.accepted_checks`. Those two belong to the
   earlier draft-decision chain. They are in the import closure and supply
   shared definitions (`recovered`, `tag`, `width`, `salt`), but as far as I read
   the bound does not use them at theorem level. The two `authenticated`
   theorems have the same conclusion and the same exceptional event, so the
   pair-binding finding stands in substance. The point matters for section 3.3:
   R1's frozen-order Merkle model is an in-place level traversal
   (`verifySlot_frozen`, recovered through `slot_path`). It is not
   `BinMultiproof.Accept`, which is the relation `AspisPairResidualMerkle` builds on.
6. **The collision envelope 1,161 belongs to the model verifier, checkpoint
   included.** It equals sampler 115 + slots 477 + 563 + checkpoint 6. The paper
   count for Aspis's model verifier is **1,111 at the branch head** and **1,112 at
   the devnet source 8a4059c8bc2**. The devnet source has a fresh start frame, which
   the head removed. Both are counted from the Rust in section 2.2. Neither is
   proved: the Aspis model decision and its budget lemma do not exist.

## 1. The game

### 1.1 R1's game, quoted

From SOUNDNESS-CLAIM-DRAFT-20261108 (at 895d1f371c9) sections 1.1, 1.4, 3.3 and
the Lean:

- **Adversary.** `SCE_Experiment.Adversary A` (RPz8_SCE_Experiment.lean):
  ```lean
  structure Adversary (A : Type) where
    first : Program Bytes State (FirstInputs A)
    second : FirstInputs A → alloc.vec.Vec U8 → Heap (Nat → Record) → A →
      Program Bytes State (SecondInputs A)
  ```
  It is fixed before the oracle, and every phase is an arbitrary oracle program.
  The second phase receives TX1's saved checkpoint bytes, post-copy heap and
  allocator state. `FirstInputs` holds `entry, data, state`; `SecondInputs` holds
  `entry, data, slot, state`. The adversary chooses every account image and the
  instruction data of both entries. The upload transactions that fill the proof
  buffer are abstracted into that choice. The headline evaluates
  `a⊤ := NNH_StateNormalize.normalize a`, which is `a` with both allocator
  outputs set to `true` (owner decision 2026-11-07, RZ-STATE).
- **Phases.** `GExq_AccountExperiment.program` runs `adversary`, then the
  installed TX1 wrapper (`GExq_InstalledWrapper.first`). On
  `.ok (.Ok (saved, post, final))` it runs `chooseSecond input saved post final`
  and then the installed TX2 wrapper. Otherwise it stops with `none`.
  `SCE_Experiment.accepted` is true iff both wrapper results are `.ok (.Ok _)`.
- **What is counted in Q.** `ARW_Induced.issued native1 copy allocator id a H` is
  the adversary's issued digest calls in both reached phases, with duplicates and
  response order kept. Phase 2 is counted only if the native TX1 wrapper returned
  Ok. The native wrapper computation counts as pure, so "only the adversary's
  issued calls are charged to P". Every call made before a rejection is counted.
  The statement parameter `queries` (L154) is the all-pairs form
  `∀ J K, (ARW_Induced.issued (stage1_owned … (envInst J …)) … (normalize fx.a) K).length ≤ fx.Q0 + fx.Q1`.
  The verifier's own calls are not in Q. They enter as the constants 34, 1,161,
  1,921 and 2,965.
- **What Runs asserts.** `RSL.TASB.Runs` (TAS_TopB.lean) has six fields:
  `frame : S.GameFrame c`, `trace : S.TraceRep c I.entry`, `ok1`/`out1` and
  `ok2`/`out2` (both entries returned `Ok ()` with their recorded outputs). At
  the host, `GameFrame` is `NNH_RecordSig.GameFrame` ∧ `NOC_Run5bHost.retained`.
  - `NNH_RecordSig.GameFrame`: (a) `next t u` (consecutive on one bank lineage)
    and the two entry identities; (b) the checkpoint handle of TX1 (account 2) is
    the handle of TX2 (account 6), with equal physical keys, and it is not in
    `intervening t u`; (c) `success t` (TX1's parent status); (d, non-trace part)
    `copied t = saved` and `actions t = recorded actions`.
  - `retained`: `RuntimeEntrypointAdmission … w1 3 ∧ RuntimeEntrypointAdmission … w2 7 ∧
    CPR_DataPersistence.TwoTransactionLaw …`.
- **Failure event and averaging.** `deployed_charge` bounds
  `E_H max (r H) (ind (Runs ∧ ¬ OutcomeRec))`. Here `r` is the extractor-failure
  mass (`RawRecordedOracleExtractionMassBin.failureMass`: accepted, and
  `RawRecordedPublicSpendExtractorBin.extract` returns `none`) plus the
  query-scan term. `E_rec` is charged once
  (`BinRawByteCollisionTargets.event … (Q0+Q1+2965)` on `a⊤`'s own account run).
  Nothing is conditioned and no H is excluded.

### 1.2 The one-transaction game for Aspis (statement; not compiled)

The adversary power, the work metric and the failure event are unchanged.
Only the second phase is removed.

```lean
/-- One adversary, fixed before the oracle, choosing every account image and
the instruction data of the single entry (the 7-account Aspis entry). -/
structure Adversary1 (A : Type) where
  run : Program Bytes State (GExq_AccountExperiment.FirstInputs A)  -- entry, data, state

/-- The single installed wrapper: the extracted Aspis `stage2_owned`
(future-one-tx). NOT AVAILABLE: no extraction of the Aspis entry exists. -/
-- W1 : … → Entry → Program → Slice U8 → A → SdkC_Oracle-program with reply type
--   Result (core.result.Result (Heap (Nat → Record) × A) AdapterRw.Cuts.PE)

def program1 (W1 …) (a : Adversary1 A) : Program Bytes State (Outcome1 A) :=
  bind a.run fun input =>
    bind (SdkC_Oracle.program (W1 … input.entry id input.data input.state)) fun reply =>
      .done (input, reply)

def accepted1 (o : Outcome1 A) : Bool :=
  match o.2 with | .ok (.Ok _) => true | _ => false

/-- What is counted: every digest call the adversary issues, duplicates and
calls before rejection included. -/
def issued1 (a : Adversary1 A) (H : Bytes → State) : List (Bytes × State) := (eval H a.run).1

-- statement parameter, same quantifier shape as L154 restricted to what remains:
-- queries1 : ∀ K, (issued1 (normalize1 fx.a) K).length ≤ fx.Q

structure Runs1 (c) : Prop where
  frame : (d.e c = CPG_Projection.entry (r.p c) (r.t c) ∧ (r.p c).actions (r.t c) = r.actions c)
          ∧ RuntimeEntrypointAdmission L c.entry c.world.w 7
  trace : TraceRep c I.entry        -- every invoke is the entry at the RSL images;
                                    -- every non-verifier action is the recorded Pool/runtime action
  ok    : ∃ s', (I.entry (args c) (state c) (env c)).exit = .ret (.ok (), s')
  out   : Out c (I.entry (args c) (state c) (env c))
```

The failure indicator is `max (r H) (ind (Runs1 ∧ ¬ Outcome1))`, with the same
`r` (accepted, and the extractor returns none, plus query scan). Whether
`Outcome1` and an account-run event stay is decision D2.

Notes on equivalence of power and metric:

- In R1, `issued` depends on the environment digest `J` only through the native
  TX1 wrapper, which decides whether phase 2 runs. With one phase that dependence
  is gone, so the all-pairs form `∀ J K` collapses to `∀ K`. The counted quantity
  is the same: every call the adversary issues.
- R1's second phase sees TX1's outputs before choosing TX2. Aspis has no
  intermediate output. The one-phase adversary can still run any computation on
  the oracle before submitting, and every such call is in Q. Nothing the R1
  adversary could adapt to exists in the Aspis execution. This is not a
  restriction of the adversary.
- The proof buffer is filled by upload transactions before the entry. In R1 and
  in Aspis this is modelled the same way: the adversary chooses the buffer image
  in `entry`. No persistence hypothesis covers the upload. Under the game, the
  buffer is whatever the entry reads.

### 1.3 R1's runtime hypotheses, one by one

| R1 hypothesis (where) | Aspis | Reason |
|---|---|---|
| `RuntimeEntrypointAdmission` at TX1, 3 accounts (`retained` conj. 1) | **no longer needed** | no TX1 (stage 1 returns `InvalidInstructionData` under `future-one-tx-lean`, owned.rs:478-482) |
| `RuntimeEntrypointAdmission` at TX2, 7 accounts (`retained` conj. 2) | **still needed**, same row, same 7-account entry | `stage2` snapshots 7 accounts (owned.rs:513-521); the seventh is still checked (owner, read-only, size `checkpoint_size(S2)`, owned.rs:247) and copied, but its bytes are not read |
| `RuntimePersistence` (`CPR_DataPersistence.TwoTransactionLaw`, `retained` conj. 3) | **no longer needed** | no state passes between verifier transactions. Pool accounts are read as they are at the entry and bound into the settled statement (section 7 of SOUNDNESS-ARGUMENT.md); persistence of Pool state across spends is settlement/double-spend, not soundness |
| GameFrame (a) `next t u`, one bank lineage | **no longer needed** | one transaction |
| GameFrame (b) same checkpoint account, equal keys, not in `intervening t u` | **no longer needed** | no checkpoint |
| GameFrame (c) `success t` (TX1 parent status) | **no longer needed** | no TX1 |
| GameFrame (d) `copied t = saved` | **no longer needed** | no checkpoint copy |
| GameFrame (d) `actions t = recorded actions`, and the entry identity | **still needed**, for the single transaction | the trace association is how Pool's CPI and runtime actions enter the theorem |
| `TraceRep` | **still needed**, one transaction | same role |
| `ok1/out1`, `ok2/out2` | **replaced** by `ok/out` of the single entry | success antecedent |
| `R9PoolRuntimeBinding.P2Prime` (proved by `P2P_Charge.binding_or_collision` at the account event; not a trust row) | **no longer needed** | it says TX2 read the same buffers TX1 digested; there is no second read |
| `S2X.CheckpointVersionBinding` (constructed from RuntimePersistence) | **no longer needed** | no checkpoint |
| `RuntimeClockSlotBinding` | **still needed**, same call site | `Clock::get()` at owned.rs:522 feeds `entry.is_active_at(current_slot)` (owned.rs:170, :222) |
| `RuntimeReturnDataClear` | **still needed**, same call site | `set_return_data(&[])` at owned.rs:505 |
| `RuntimeReturnData` | **still needed**, same call | `emit_result` (r1_pool_adapter.rs:927) |
| `RuntimeMemcmp` | **still needed if** the compare in `scan_proof_buffer` compiles to `sol_memcmp_` as in R1 | `scan_proof_buffer` is shared code; only `proof_length` changes under `future-one-tx` (r1_pool_adapter.rs:780-810). The compare length is the afterstate prefix; re-check at the Aspis ELF |
| `RuntimeSyscall`, `RuntimeSha256Value`, P1 | **still needed**, unchanged | every digest is `SolanaDigest` → `hashv` (lib.rs:10-30). `digest_into` (used by the merged multiproofs) is a new source call site of the same syscall. That is a refinement item, not a new row |
| Allocator (instantiated; RZ-STATE normalisation) | **still needed**, one phase | the single wrapper still returns an allocator state |
| PDA derivation (`fx.pda`, universal environment data) | **unchanged** | `create_program_address` is called (owned.rs:111-160, :264, :289, :305). R1 treats it as universal environment data, not as oracle queries. Aspis keeps that modelling |
| Entry-route analysis `[3,10]/[3,11]` | **different one needed** | the deployed route set is close-checkpoint, stage 1 (always rejects under `future-one-tx-lean`) and stage 2 (r1_pool_adapter.rs:1008-1010, behind `pool_route::admitted`). A reachability statement for that set replaces R1's |

Nothing is added. No new runtime trust row is needed for the one-transaction
game as stated.

## 2. The terms of total(Q)

`total(Q) = (Q+34)·B + collisionLoss(Q) + accountLoss(Q) + 2^-126 + 2^-454`
(`F3T_Numeric.total`), with `collisionLoss(Q) = 6(Q+1161)²/2^256` and
`accountLoss(Q) = 6(Q+2965)²/2^256`. The numeric path from `failure_bound` to
`total` is 4 modules: `OraclePortHeadlineFrozen2PerAttempt` (header: "Two-transaction
per-attempt endpoint … includes the six checkpoint reads"), `Uni_CanonicalPerAttempt`,
`RPz7_EndP_Numeric`, `RPz7_F3T_Numeric`. The arithmetic carries over in form,
but each is stated for `dV_frozen2`, `AcceptedRunJoin` at `dV_frozen2`, and the
`Q+34`/`Q+1161` constants.

### 2.1 Start term

This is redone per step by the other agents (PER-STEP-ACCOUNTING.md and the
40-row instance). It is not redone here.

### 2.2 Collision envelope (1,161)

**Where it comes from in R1 (Lean).** `OraclePortExperiment.verifier_budget`
gives the sampler prefix plus a `Decision` budget of 1,046
(`OraclePortExperiment.Budget`, "an all-input issued-call obligation, including
rejected executions"), for a total of 1,161. For `dV_frozen2`,
`OraclePortFrozen2.decision_budget` proves 1,046 = `batch0_bound` 477 +
`after_bound` 569. `after_bound` is 563 (`batch1_bound`) + 6 (`checkpoint_reads`).
The per-slot bound is `OraclePortFrozen2Resource.slot`:
`2·|positions| + capacity − 1`. With capacities 146/146/128 (batch 0, 10 positions)
and 172/172/150 (batch 1, 12 positions), batch 0 is 165+165+147 = 477 and
batch 1 is 195+195+173 = 563. The sampler prefix is 115. So
**1,161 = 115 + 477 + 563 + 6**: a property of the model verifier program,
checkpoint digests included. It is not a property of the adapter or Pool.
`OraclePortFrozen2.distinct_bound` turns it into `firstReads ≤ Q+1161` on the
recorded experiment, and `AcceptedRunJoin` transports it to the deployed run.

**Aspis, paper count from the Rust (head 01f5312ca0e).** Every digest on the
entry path goes through `SolanaDigest` (lib.rs:10-30). The adapter path
(`validate_asq8`, `authenticate_asq8_accounts`, `scan_proof_buffer`,
`reconstruct_asq8_statement`, `validate_pool_v1_pair_forest_terminal_statement_v1`,
`emit_result`) makes no digest call. I grepped `hashv`, `digest` and `Digest32`
in r1_pool_adapter.rs, r1_pool_adapter_owned.rs and aspis-statement. The only
`sha2` uses there are under `#[cfg(test)]`, and the PDA derivations are the
separate `create_program_address` call. So the count is the count of
`verify_summed_format`:

| Part | Source | Issued digests |
|---|---|---:|
| semantic transcript init | r1_wire.rs:267 | 1 |
| rows 0–26 (absorb, squeeze, advance) | r1_wire.rs:288-290 | 27·3 = 81 |
| opening transcript start `Transcript::new` | transcript.rs:12, verifier.rs:86 | 1 |
| rows 27–30 (`scalar` = absorb + block + advance) | verifier.rs:87-92, transcript.rs:19-26 | 4·3 = 12 |
| row 31 queries (absorb + 8 block pairs) | transcript.rs:40-56 | 1 + 16 = 17 |
| row 32 ρ (`scalar_k`) | verifier.rs:97 | 3 |
| **= R1's `prepare`, unchanged** | | **115** |
| final sumcheck start | fused.rs:522 `Transcript::resume`, no hash (head). At devnet source 8a4059c8bc2: `Transcript::new`, 1 | 0 (1) |
| rows 33–39 (`scalar_k` each) | fused.rs:523, :530 | 7·3 = 21 |
| leaves, every key hashed before the duplicate check | fused.rs:782 (`batch_leaf`, candidate.rs:158) | 3·22 = 66 |
| merged multiproof parents, C1 and C2 | `verify_counting_merged`, one digest per computed parent | 2·(22 + 296 − 1) = 634 |
| merged multiproof parents, folded tree | same | 22 + 254 − 1 = 275 |
| checkpoint | none | 0 |
| **total** | | **1,111 (head); 1,112 (devnet)** |

The parent count uses R1's bound form (`OraclePortFrozen2Resource.slot`:
leaves + capacity − 1 parents per slot) at the merged capacities 296/296/254.
SOUNDNESS-ARGUMENT.md section 6.3 reached the same 909 by summing distinct
parents per level. **The 1,112 on paper stands for the devnet source. At the
branch head it is 1,111.** Both are below 1,161, and the adapter adds nothing.
Status: PAPER COUNT. To make it a theorem, an Aspis model decision is needed
(section 4, items M3 and M5), with a budget lemma `≤ 975` for the decision and a
40-row sampler-prefix lemma `≤ 136`. R1's `OracleDecisionPrereqSampler` counts
115 for 33 rows. Aspis can keep 1,161 as an upper bound without changing the
collision term, because `kappa` is monotone in the count. That needs those two
lemmas, not the paper count.

The issued-call log of the model's recorded experiment would be at most
`Q + 2·1,111` by the same `recorded_length` argument (section 0, item 3).

### 2.3 Account term (2,965)

**What the recorded reads are.** `P2P_Charge` says: "The four binding reads are
already included in 2965: 1921+1040+4."

- **1,921**: `RawJ_AccountBudget.budget` bounds the issued calls of the actual
  two-phase account program by `Q0+Q1+1921`, with 1,018 for the installed TX1
  wrapper and 903 for TX2 (`RawJ_InstalledBudget.first`/`.second`). These are
  source-level bounds on the extracted wrappers. They are larger than the model
  counts per transaction (595 and 566), and I did not reconstruct why.
- **1,040**: `SdkC_Replay.replay p q := OraclePortFrozen2.batch p q slots`, a
  canonical replay of all six Merkle slots from the parsed proof projected out
  of the account run's output (`replay_bound`: 477 + 563).
- **4**: the audit reads of `Hist_AuditQueries`: `hash written.proof`,
  `hash written.pub`, `hash current.proof`, `hash current.pub`. Through
  `R9PoolRuntimeBinding.P2Prime` they give "TX2 read the same buffers TX1
  digested" unless a collision occurs.

**Why R1 needs them.** The headline's conjunct 4 (`OutcomeRec`: Outcome with its
bad event set to `E_rec`) is evaluated on the adversary's own account run
(`ARQ_Observer.select`). This is the actual two-phase program, not the model
verifier's recorded experiment. Its binding facts (root recovery at the selected
occurrence, the P2′ same-buffer fact) need a collision-free event on that run's
log. The model's collision term covers only the model log.

**Does a one-transaction run have an analogue?**

- The four audit reads have no analogue. There is no written/current pair: the
  proof buffer is read once, and nothing is digested in one transaction and
  re-read in another.
- The account run's issued calls: one installed wrapper. Paper count is
  Q + 1,111 at the head (section 2.2; the adapter issues no digest). The Lean
  source bound will be whatever the extracted Aspis wrapper's budget lemma proves.
  R1's source bounds exceed its model counts, so the paper count is not a
  prediction of that lemma.
- Replay: if the account event keeps a canonical replay, the replay of the three
  merged slots is 339 + 339 + 297 = 975 (paper).
- Hence **if** D2 keeps the split-B form, the analogue's paper count is
  Q + 1,111 + 975 + 0 = **Q + 2,086** at the head (Q + 2,087 at devnet). That is
  below 2,965. **If** D2 drops the separate account event, the account term goes
  away only if the Aspis outcome facts are proved on the model log through the
  accepted-run join. Whether they can be is not established.

Status: paper counts. The derivation needs an extracted Aspis entry.

### 2.4 Abort term (2^-126) and query-scan term (2^-454)

- The abort term comes from the extractor (`shared_oracle_failure_le_hit_add_abort`,
  `bankAbortMass_le`) and is stated on R1's 33-row run view. It carries if the
  Aspis extractor is R1's, applied to the 33-row projection of the 40-row run.
  That projection lemma belongs to the 40-row charged experiment (plan item 13).
  It does not exist.
- The query-scan term is `QueryScanModelFailure.exhaustion_bound (2^18)`. It
  carries: the row-31 query derivation is unchanged (transcript.rs:40-56). Its
  transport sits in the same composition.

Neither term depends on the two transactions.

## 3. From acceptance to the model-level checks

### 3.1 R1's statements, quoted

The chain the bound uses (section 0, item 5):

```lean
-- OraclePortFrozen2ActualChecks
theorem accepted_checks (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State)
    (Q : Nat) (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (accepted : (run D P H).2.2 = true)
    (clean : ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
      BinRawByteCollisionTargets.pred (Q+1161)) emptyTable (run D P H).1) :
    ∃ p q, OraclePortStoredParserC4.parseReached (input P H).stored (reached D P H) = some p ∧
      queries (reached D P H) = some q ∧
      Nonempty (LiteralAcceptanceTerminal.Checks (input P H).statement
        (OraclePortReaderPlumbingC6.reword
          (BinCompiledRunWordStability.wordsFromRun D (view (run D P H)))
          (OraclePortStoredDecisionDraftC4.typedRows p q (reached D P H))))

-- OraclePortFrozenOrderChecks (the containing-log form)
theorem accepted_checks (H) (stored) (tr) (m) (p) (q) (parsed : parseReached stored tr = some p)
    (query : queries tr = some q) (accepted : (eval H (dV_frozen stored tr m)).2 = true)
    (log) (Q) (consistent : ∀ a ∈ log, a.2 = H a.1)
    (contains : ∀ a, Read (eval H (OraclePortShortCircuit.short (slotPrograms p q slots))).1 a → Read log a)
    (bound : firstReads emptyTable log ≤ Q)
    (clean : ¬ hitsBad (AllAddressCollision.bad … BinRawByteCollisionTargets.pred Q) emptyTable log)
    (frames : Fin 3 → Bytes) (selectors : Fin 3 → Fin 5) (frameRead : ∀ k, Read log (frames k))
    (rootRead : ∀ k, BinRawByteCollisionTargets.pred (selectors k) (frames k) = some (committedRoot p k.val)) :
    Nonempty (LiteralAcceptanceTerminal.Checks tr.statement (reword (maps log frames p) (typedRows p q tr)))

-- OraclePortFrozenOrder.authenticated (the three-tree recovery)
theorem authenticated (H) (stored) (p) (parsed : parse stored = some p) (q)
    (accepted : (eval H (OraclePortShortCircuit.short (slotPrograms p q slots))).2 = true)
    (log) (Q) (consistent) (contains) (bound : firstReads emptyTable log ≤ Q) (clean : …)
    (kind : Nat) (kindBound : kind < 3) (frame : Bytes) (j : Fin 5) (frameRead : Read log frame)
    (rootRead : BinRawByteCollisionTargets.pred j frame = some (committedRoot p kind)) :
    ∀ pos, pos < 22 → recovered log frame p kind (index q kind pos) =
      some (OraclePortPackedChoiceC4.payload p kind pos)

-- OraclePortFrozen2Roots.targets: the three roots are read, by the collision-target
-- predicates (trailing for kinds 0, 1; offset 38 for kind 2), from the actual sampler
-- frames of rows 0, 2 and 30 of the reached transcript.
theorem targets (D) (P) (H) (ha : (run D P H).2.2 = true) (p) (q) (parsed) (query) :
    ∀ k : Fin 3, BinRawByteCollisionTargets.pred (selectors k) (frames D P H k) =
      some (committedRoot p k.val)
```

Supporting pieces: `OraclePortObservationTransportC6.ofTyped` (typed acceptance
gives `OraclePortSelectedConsumerC6.Checks` on the opening words) and
`.transport` (the checks carry to recovered words under agreement at the selected
initial fibres, opened values and folded fibres, through
`OraclePortSelectedObservationsC6.observe_withWords`). Then
`OraclePortSelectedConsumerC6.toLiteral_nonempty` turns them into the literal
`Checks`. `OraclePortFrozen2.acceptance_eq` shows that `dV_frozen2`'s verdict
equals the checkpoint-free `dV_frozen`'s. The checkpoint is therefore already
gone at the model level, before any of the above. R1's typed acceptance is
`D0TypedChecks.verify rs i`: `read = some i.data ∧ LiteralPairingChecks.checks rs ∧
R16DecisionQueryModel.verify data queryBytes ∧ EquationEndpoint ∧ ClosedSum`.
`R16DecisionQueryModel.verify` is the per-query first-fold check (the `Writer`
field). `ClosedSum` is R1's already-batched second-fold check, half of `Backend`.

### 3.2 The theorem that fixes the opened values before ρ, and what it rests on

This is where the earlier version went wrong, so it is stated exactly. In R1's
model the values the row-32 event reads are fixed before ρ by the conjunction of
four facts, each a Lean theorem in L187:

1. **Opened = recovered from the log before the commitment frame.**
   `OraclePortFrozenOrder.authenticated` via `recovery_at_index` and
   `BinRawByteCutRecovery.recover_at_first_commitment`: at every queried
   position, for each of the three kinds, the opened payload equals
   `recoverAt … (cut log frame) …`, a function of the log strictly before that
   root's commitment frame.
2. **The commitment frames are the transcript frames of rows 0, 2, 30.**
   `OraclePortFrozen2Roots.targets`.
3. **The recovered maps are the words the recorded transcript carries.**
   `OraclePortFrozen2ActualChecks.maps_eq_builder`: they equal
   `BinCompiledRunWordStability.wordsFromRun D (view run)`.
   `BinRawByteCutStability.recover_stable` says these are already fixed at the
   first commitment read, simultaneously for every path, under one collision
   event.
4. **The row-32 event reads only the prefix.** `LiteralRhoDensity.read P` takes
   `(d, q)` from rounds 25–31 (`beforeRho`) and row 31. For Aspis this is
   `AspisPairResidual.Row32.bad P` (PSC), the same reader. Row 32's challenge is
   sampled after all of them on the duplex chain.

**What it rests on:**

- (i) acceptance of the model Merkle slot programs (the source counterpart is
  `AcceptedRunJoin`, outside the model);
- (ii) the slot reads being in the log (`slots_read`);
- (iii) `firstReads ≤ Q+1161` on that log (`distinct_bound`, which needs the
  decision budget);
- (iv) one exceptional event, `AllAddressCollision.bad iv BinRawByteCollisionTargets.pred (Q+1161)`,
  charged once as the collision term.

There is no other hypothesis.

**For Aspis:**

- Facts 2, 3 and 4 carry with the 40-row transcript. Rows 0, 2, 30 are
  byte-identical, and `AspisRows40Literal.transcript_take33` (PSD) gives the
  prefix.
- Fact 1 needs the merged form. `AspisPairResidual.Merkle.merged_query_recovery`
  (PSC, compiled) proves it for `BinMultiproof.Accept`. R1's frozen-order chain
  instead uses its in-place slot program `verifySlot_frozen` and `slot_path`.
  So the Aspis copy of `authenticated` has two routes:
  - **(a) Copy the in-place model with 22 positions.** `verifySlot_frozen` with
    positions `List.range 22`, `wellFormed` bound 16 → 22, capacities
    296/296/254, summed-format slot offsets. Then copy `recovery_at_index`. The
    path lemmas (`slot_path`, `inPlace_path`, `levels_path`, `leaves_retained`)
    do not mention the batch size, so they look reusable. I read them, but did
    not compile them. The Rust `verify_counting_merged` is the same single-pass
    in-place traversal, so the later source refinement stays R1-shaped.
  - **(b) Keep PSC's form.** Add a lemma "an accepted in-place merged slot gives
    `BinMultiproof.Accept` with its trace in the log". I did not find this lemma
    in R1.

  Recommendation: (a). It is a copy with changed constants, and it matches both
  R1's chain and the Rust.
- Fact (iii) needs the Aspis budget lemmas of section 2.2.

### 3.3 The statement an Aspis counterpart must have (not compiled)

Layer 1, selected checks (copy of `OraclePortSelectedConsumerC6.Checks`). All
R1 fields stay up to `queryDecode`, plus `semantic`. `writer` and `backend` are
replaced by:

```lean
  firstBatch : ∑ j : Fin 22, (LiteralOpeningView.eK (SelectedChallengeMap.rhoOf rho)) ^ j.val *
      ((observe data queries).first j - (observe data queries).opened j) = 0
  pairing23  : (P2) ∧ (P3) of MatchingSupport.AcceptedPairing (observe data queries).scalars
  -- rows 33..39, as in ASPIS-INSTANCE-PLAN.md §2.3, with every quantity read from
  -- `observe data queries` (scalars.f, relW scalars, second, basis queries) and rs[33..39]:
  m33 claimS rhs2 lam state33, entry33, valid40_33, read33 : aspisRead33 (rs.take 33) m33 = some (…)
  rounds, entryRound, validRound, readRound : ∀ b, aspisReadRound (rs.take (34+b)) m_b = some (…)
  rhs2Def : rhs2 = ∑ j, (eK (rhoOf rho))^j * (observe data queries).second j
  finalCheck : finalClaim … = foldAll … f … * (foldAll … (relW …) … + eK lam * foldAll … (qweight …) …)
```

`firstBatch` is stated on the observation record, so by `pair_eq_pairOf` (PSC) it
is PSC's batched first-fold equation on `firstResiduals`.

Transport theorem (copy of `.transport`): same three premises (`initial`,
`opened`, `folded`), same conclusion on `reword w rs`. Proof: R1's
`observe_withWords` **unchanged**, plus "rows 33–39 are untouched by `reword`"
(`AspisRows40Literal.enrich_final`, PSD). Every new field is a function of
`observe` and of rows 33–39. PSC's `pair_withWords`/`pairBad_withWords` are the
same fact specialised to the pair.

Layer 2, accepted ⇒ checks on the actual recorded rows (copy of
`OraclePortFrozen2ActualChecks.accepted_checks`):

```lean
theorem aspis_accepted_checks (D : AspisDecoder40) (P : Prover) (H : Bytes → State)
    (Q : Nat) (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (accepted : (run40 D P H).2.2 = true)
    (clean : ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
      BinRawByteCollisionTargets.pred (Q+1161)) emptyTable (run40 D P H).1) :
    ∃ p q, parseSummed (input P H).stored (reached40 D P H) = some p ∧
      queries (reached40 D P H) = some q ∧
      Nonempty (AspisChecks (input P H).statement
        (OraclePortReaderPlumbingC6.reword
          (BinCompiledRunWordStability.wordsFromRun40 D (view (run40 D P H)))
          (typedRows40 p q (reached40 D P H))))
```

Here `run40 D P H := eval H (original D dV_aspis P)`. `dV_aspis` is the Aspis
model decision: admission guard, `parseSummed`, R1's `queries`, three merged
in-place slots, and `AspisTypedChecks.verify`. `AspisChecks` is the
acceptance-link agent's 40-round structure (ASPIS-INSTANCE-PLAN.md §2.3). The
`(Q+1161)` may stay as R1's constant, given the budget lemmas.
`aspis_checks_noHit_r1_checks` (PSA) then gives R1's `Checks` on `rs.take 33`.

Layer 3: `CheckedAcceptance40` (copy of `OraclePortFrozen2C6.checked_acceptance`
and `OraclePortFrozen2Consumer.fibre_checks`), consumed by the Aspis copy of
`Frozen2StartChargeClean`.

### 3.4 Which R1 modules apply unchanged, which need a copy, what is new

- **Unchanged:**
  - `BinRawByteCutRecovery`, `BinRawByteCutStability`, `BinRawByteCollisionTargets`,
    `AllAddressCollision`, `BinCombinedMerkleCollision`;
  - `OraclePortSelectedObservationsC6` (`observe`, `observe_withWords`),
    `OraclePortMapObservationsC6` (`initial_fibres`, `final_selected`),
    `OraclePortPackedChoiceC4`, `OraclePortCandidateWordsC6.reader_words`;
  - `OraclePortStoredDecisionDraftC4.{packed, words, restore, typedRows}`. `restore`
    is the identity on payload rows other than 2 and 30;
  - `OraclePortReaderPlumbingC6.reword`, `OraclePortAllSelectedRecoveryC6.{recovered, tag, width, salt, leaf_fields}`
    (opening layout unchanged: C1 `take 480`, C2 `slice 480 128`, folded
    `slice 672 128`, salts at 608/640/800);
  - `LiteralMatchingData.read`, `LiteralOpeningView.read`, the semantic projection;
  - PSC's `AspisPairResidual*`.
- **Copy with a changed instance:**
  - `OraclePortFrozenOrderSlot`/`…SlotPath`/`…Leaves`/`…RecoveryLevels`/`…RecoveryStep`:
    22 positions, `wellFormed` ≤ 22, merged capacities and offsets; the path
    proofs are probably reusable as they stand;
  - `OraclePortFrozenOrderCutRecovery`, `OraclePortFrozenOrderSelectedRecovery`:
    one slot per kind, no `batchOf`;
  - `OraclePortFrozen2Resource.slot`: bound 2·22 + cap − 1;
  - `OraclePortFrozenOrderDecision.dV_frozen`. The Aspis decision is modelled on
    `dV_frozen`, not on `dV_frozen2`, since there is no checkpoint;
  - `OraclePortStoredParserC4`/`…WidthsC4`/`OraclePortSelectedDraft` constants:
    the summed-format layout;
  - `OraclePortFrozen2Reached`, `OraclePortFrozen2Roots`: the 40-row reached
    transcript, rows < 40 in `frame_read`;
  - `OraclePortFrozenOrderChecks`, `OraclePortFrozen2ActualChecks`,
    `OraclePortFrozen2CanonicalChecks`, `OraclePortRowsCanonicalC6` (the
    canonical schedule becomes `valid40`), `OraclePortFrozen2C6`,
    `OraclePortFrozen2Consumer`, `OraclePortStoredExperimentC4.Budget` and
    `OracleDecisionPrereqSampler` (40-row prefix).
- **New:**
  - `AspisTypedChecks.verify`: R1's `D0TypedChecks.verify` with
    `R16DecisionQueryModel.verify` (per query) replaced by the batched first-fold
    closed sum, the (P1) conjunct of `LiteralPairingChecks` replaced by the
    rows-33–39 reads and final check, and `ClosedSum` replaced by `rhs2Def`;
  - its `ofTyped` (typed acceptance ⇒ layer-1 checks, with the rows-33–39 reads
    shown total on accepted transcripts);
  - the layer-1 structure and its `toAspisChecks`.
- **Not needed (two-transaction only):**
  - `OraclePortFrozen2Decision` (`afterBatch0`, `stage2`, `acceptance_eq`),
    `OraclePortFrozen2Checkpoint`, `OraclePortFrozen2Bounds.after_bound` (the +6),
    the `OraclePortCheckpoint*` family (7), `R16DecisionCheckpoint`;
  - `R9Pool*` (`P2Prime`, saved-ten model, checkpoint codec);
  - `OraclePortSixSlotBudgetC3`, `QvStage1Count`/`QvStage2Count`;
  - `OraclePortFrozen2Trace`. By name and imports it is the stage trace; I did
    not read its body.

**What is new because of one multiproof per tree:** the merged slot program, its
recovery at 22 positions, and its budget. R1 needs two slots per tree because of
its two-batch split across the transactions. Duplicate folded indices are handled
the same way: `hashLeaves` rejects equal index with unequal digest, and so does
fused.rs:783-787. The leaf hashing is unchanged.

## 4. Size and order

Model level (provable now in Lean against the R1 objects and the PSC/PSD files):

| # | Module (new name, AspisOneTx…) | Kind | Depends on |
|---|---|---|---|
| M1 | SummedParse: layout of the summed format into R1's `Parsed` fields (openings, roots, wire), merged slot offsets, certificate | copy, changed instance | — |
| M2 | MergedSlot: in-place slot over 22 positions; `slot_path` | copy, changed constants | M1 |
| M3 | MergedResource: slot bound 2·22+cap−1; decision budget ≤ 975; 40-row sampler prefix ≤ 136 | copy + small new | M2, PSD sampler |
| M4 | TypedChecks: `AspisTypedChecks.verify`, reads of rows 33–39 | **new** | PSA `AspisChecks` shape, PSD protocol |
| M5 | Decision: `dV_aspis` (guard, parse, queries, three merged slots, M4); `Budget` | copy, changed | M1–M4 |
| M6 | SelectedRecovery: merged `recovery_at_index`, `authenticated` | copy, changed | M2 |
| M7 | Roots/Reached: `targets`, `accepted`, `slots_read`, `distinct_bound`, `frame_read` on the 40-row run | copy, changed | M5, PSD `transcript_take33` |
| M8 | SelectedChecks: layer-1 structure, `ofTyped`, `transport`, `toAspisChecks` | **new** structure, proofs copied | M4, PSD `enrich_final`, PSA |
| M9 | ActualChecks: layers 2 and 3 (`aspis_accepted_checks`, canonical schedule, `CheckedAcceptance40`, `fibre_checks`) | copy, changed | M6–M8 |
| G1 | Game: `Adversary1`, `program1`, `accepted1`, `issued1`, `Runs1` over an abstract installed wrapper | copy with the second phase removed | — |
| G2 | Per-attempt endpoint for one transaction (copy of `OraclePortHeadlineFrozen2PerAttempt` at `dV_aspis`, without the checkpoint) and the numeric path | copy, changed | M9, the 40-row bound layer |

Order: M1 → M2 → {M3, M6} → M4 (needs PSA's `AspisChecks`) → M5 → M7 → M8 → M9
→ G2. G1 can start at any time.

Source refinement (needs the Aspis Rust extracted; out of scope here):

- `AcceptedRunJoin` for `verify_summed_format` against `dV_aspis`. This includes
  `verify_counting_merged`/`merkle_verdict`/`merged_tree` against M2, `fold_sums`
  against the batched closed sums, and `summed_final_checks` against the
  rows-33–39 model.
- `StoredCarrierBinding` for the one-transaction runtime.
- The extracted installed wrapper `W1` of the one-transaction `stage2_owned`,
  with its issued-call budget (the account-run count of 2.3).
- The entry statement of SOUNDNESS-ARGUMENT.md section 7, and the route
  reachability statement.

**The single hardest item: M4 together with M8.** M4 is the typed batched check
with the reads of rows 33–39 shown total on accepted transcripts. M8 shows that
the resulting fields survive `reword` and assemble into `AspisChecks`. This is
the one place where the new acceptance predicate meets R1's consumer. In R1 the
corresponding modules needed `backward.isDefEq.respectTransparency` and local
irreducibility to compile. Everything else is a copy with changed constants. In
the whole layer, the largest risk is the source-level `AcceptedRunJoin`, which is
outside this scope.

Rough size of the model part: about 14–18 new files (M1–M9, G1–G2). About three
quarters of them are copies.

## 5. Decisions for the owner

> **Owner's answer, 2026-11-11:** "i agree to all recommendations as long as they dont push CU
> up, soundness down or risk privacy". Recorded as: D1 adopted (one-phase game, same adversary,
> metric, averaging and failure event); D2 adopted (the split-B failure event and an account term
> are kept); D3 confirmed (the same normalisation rule for the single phase); D4 to be decided
> together with R1's pending item, no new rule. D0: minutes later the owner added "but aspis is
> ultimately the release target". Recorded as a direction: the one-transaction version is the
> version intended for release, so every obligation of the security contract has to be met by
> Aspis, including the source refinement of its changed code. It is not a claim that anything is
> established, and it does not by itself move the frozen pin: the deployed two-transaction
> verifier stays the frozen target until an Aspis pin exists (names settled, source frozen, built,
> measured, deployed) and its obligations are closed. Check against the owner's three conditions, by the lead: none of D1 to D4 changes any
> code, so compute units are unchanged; none weakens the adversary, the metric or the failure
> event, D1 removes runtime hypotheses and adds none, and D2 keeps the stronger failure event, so
> soundness is not lowered; none touches the prover or anything published, so privacy is
> unaffected. These are decisions about the statement to be proved for Aspis. They establish
> nothing by themselves and change nothing in the R1 claim.

- **D0. Aspis as a release target.** The contract fixes R1's frozen two-transaction
  path. Everything here treats Aspis as an experimental candidate (AGENTS.md
  section 6). Adopting it is outside this note.
- **D1. Adopt the one-phase game for Aspis (section 1.2).**
  - *Recommendation:* adopt, with the same adversary class (an arbitrary oracle
    program choosing every input of the entry), the same work metric (all issued
    digest calls, with duplicates and calls before rejection, on `a⊤`), the same
    averaging (no conditioning) and the same failure event.
  - *Consequence:* `RuntimePersistence`, GameFrame (a)–(c), the TX1 admission,
    the checkpoint copy and P2′ leave the Aspis theorem. The TX2 admission (7
    accounts), TraceRep, ClockSlot, ReturnData(Clear), Memcmp (if still compiled
    to the syscall), SHA-256/syscall and SDK/std rows remain. No row is added.
    The all-pairs `∀ J K` in `queries` becomes `∀ K` (section 1.2).
- **D2. Keep R1's split-B failure event for Aspis.** This is the outcome conjunct
  evaluated on the adversary's own account run, together with its account-run
  collision event.
  - *Recommendation:* keep it. Dropping it changes the failure event, which
    AGENTS.md section 2 forbids without an owner decision.
  - *Consequence:* an account term remains. Its paper count is Q + 2,086 at the
    head (2.3). The P2′ audit reads disappear. The proved count waits for the
    extracted entry.
  - *Alternative:* prove the outcome facts on the model log through the
    accepted-run join and drop the separate account event. That is a different
    theorem and needs its own before/after audit.
- **D3. RZ-STATE normalisation.** R1's owner decision (2026-11-07) sets the
  allocator outputs to `true` in Q and in the pair.
  - *Recommendation:* confirm the same rule for the single phase.
  - *Consequence:* none beyond R1's.
- **D4. Campaign accounting.** This is already pending for R1 (claim draft 3.5,
  units). With one phase, MAT's phase factor c = 2 comes from the second phase
  recomputing the first, and it does not arise. The verifier calls charged per
  earlier attempt become Aspis's count instead of R1's.
  - *Recommendation:* decide it together with R1's pending item; no new rule.
- **Not a decision (recorded).** The one-transaction entry still requires a
  seventh, verifier-owned, read-only account of checkpoint size and does not read
  its bytes. This is harmless for soundness and part of the entry contract.
  Removing it would be a protocol change that alters the admission count.

## 6. Validation

- Read: ASPIS-INSTANCE-PLAN.md, aspis-instance-module-classes.tsv,
  SOUNDNESS-ARGUMENT.md, PER-STEP-ACCOUNTING.md (sections 1 head and 3),
  PAIR-BINDING.md (after the lead's message), the claim draft at 895d1f371c9
  (sections 1, 3, 4), and the L187 sources named above.
- Import closures computed with a small script over the flat L187 copy: 1,120
  modules for `OraclePortActualAcceptanceC6` and 1,186 for
  `Frozen2StartChargeProbability`. The acceptance chain is inside the latter.
- Rust read at the head: owned.rs 1-524, r1_pool_adapter.rs 780-1010, lib.rs
  10-80, fused.rs 515-560 and 760-830, transcript.rs, verifier.rs 60-100,
  candidate.rs 158 and 346-355.
- Nothing compiled, nothing built, no host job. Counts are paper counts.
- No git command that changes anything was run.

## 7. Next deliverable

M1–M3 and M6 (merged in-place slot, its budget and recovery), compiled on the
host against L187. That turns the 975 and the merged recovery into theorems in
the chain R1's bound actually uses. Then M4/M8, once the acceptance-link agent
has fixed `AspisChecks`.
