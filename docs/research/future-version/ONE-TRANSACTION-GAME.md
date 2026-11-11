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

### 1.2a The outcome: withdrawal destination, pool and deployment domain (owner, 2026-11-11)

The owner said: "make sure we have the withdrawal address locked, that was a
major oversight on r1". Named obligation: **WD (withdrawal binding)**. An
accepted Aspis spend must not pay tokens to a destination other than the one in
the public statement the proof is bound to, or for a pool or deployment domain
other than the ones it names.

What R1 has at PIN2, from the soundness lead's reading (V8-LESSONS-CHECK.md,
finding 3; not re-derived here):
- The headline `deployed_splitB` (TAS_FinalB.lean:94-113) concludes
  `Bound ∧ NNH8_Split.rest ∧ (headlineB.OutcomeRec ∨ ERec)`.
- `OutcomeRec` unfolds to `FJv_DResult.Outcome` (RPx_FJv_DBoundCaller.lean:111-151).
  Its public object (`f.semantic`, `i.decoded : R0P.Public`, R0P/Core.lean:70-76)
  carries pool, deployment domain and destination.
- No conjunct constrains those three fields. The relation is absorb-only for
  them (Core.lean:55-57).
- The headline does not reach the Pool's payment. The Pool settlement models
  `NGP_L159`, `NGK_NFO_ReadModel`, `NGK_NFR_CSettlement` and
  `NIB_ReadToSettlement` are not among its constants. R1's payout is tied to the
  proof only outside Lean, by the checkpoint hash (verifier.rs:329, checked at
  :396). R1's L159 is pending.

The two forms of the one-phase outcome:

| | Outcome |
|---|---|
| **(A) R1's outcome carried over (comparison only)** | `Outcome1 := ` the Aspis copy of `FJv_DResult.Outcome` / `OutcomeRec`, with the three fields only in the public object |
| **(B) ADOPTED for Aspis (owner: "i say yes")** | (A) **∧ PayoutBound**: for an accepted withdrawal, the Pool's settlement in the same transaction transfers exactly the statement's `amount` from the Pool vault of the statement's pool and deployment domain to the statement's `destination_token_account`. Here "the statement" is the public statement whose PIN2 serialization (pool ‖ deployment domain ‖ has-destination byte ‖ destination, pair_forest_semantic_terminal.rs:2020-2090) seeds the transcript the accepted proof is checked against. For a transfer there is no token movement to a destination (has-destination byte 0) |

`ind (Runs1 ∧ ¬ (A ∧ PayoutBound))` is at least `ind (Runs1 ∧ ¬ A)`. So (B)
strengthens the failure event and weakens nothing.

**Claimable today, and nothing stronger:** pool, deployment domain and
destination are bound into the transcript and present in the public object; the
relation does not constrain them. The paid account is tied by the entry, which
rebuilds the statement from the request the Pool pays on. That tie is outside
the relation until PayoutBound is proved. PayoutBound is OPEN; section 9.3
scopes it.

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
**Update (section 8):** the merged-slot part is now PROVED.
`AspisOneTx.mergedAll_budget` shows that the three merged slot programs issue at
most 975 digest calls on every input, rejections included (66 leaf hashes plus
at most 909 parents; 339/339/297 per tree). The 40-row sampler prefix (136) and
the verifier total (1,111) remain paper counts.
**Update (section 9):** both are now PROVED, by the rows agent at the Aspis decision:
- `AspisRec40CallBudget`: the 40-row transcript part issues at most 136 calls.
- `AspisRec40CallBudgetAspis` applies `AspisOneTx.decision_budgetS` (≤ 975):
  `verifier_issued` gives at most **1,111** calls, and `projected_first_reads`
  gives `firstReads ≤ Q + 1111` on the full experiment at `dV_aspis`.

The collision envelope for Aspis is therefore Q + 1,111 as a theorem, on the
model. Its transfer to the Rust is the accepted-run join, which is still OPEN.
Call order: the model runs rows 0–39 and then the terminal Merkle decision. The
Rust at the branch head (4045ecbdda3) has that order. The devnet-deployed build
(source 8a4059c8bc2) ran the Merkle digests before rows 33–39.

Status before section 8: PAPER COUNT. To make it a theorem, an Aspis model decision is needed
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
- **D5. Withdrawal payout inside the proved game (WD, section 1.2a).**
  - *Decided, owner, 2026-11-11:* "i say yes" (recorded by the lead in
    V8-LESSONS-CHECK.md, finding 3). Form (B) is the Aspis one-phase outcome.
    The SPL Token transfer the Pool calls is accepted as a runtime-class trust
    row for Aspis. Nothing is decided for R1; its L159 stays pending.
  - *Three-condition check:* it strengthens the statement (the failure event
    gains a conjunct, section 1.2a), changes no code (no compute-unit change),
    and touches neither the prover nor anything published. It adds one trust
    row, which is why it went to the owner.
  - *Status:* PayoutBound is OPEN, scoped in section 9.3. Until it is proved,
    the only claim is: "bound into the transcript and present in the public
    object; the relation does not constrain it".
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

Done in section 8: M1–M3 and M6 (merged in-place slot, its budget and recovery),
compiled on the host against L187. Next: M4/M8, once the acceptance-link agent
has fixed `AspisChecks`. M5 and M7 can go before them where they do not need
`AspisChecks`: the decision skeleton without its arithmetic, and the roots and
reached-run plumbing on PSD's 40-row run.

**Update (section 9):** M5, M4 and M8 are done, including "accepted ⇒
AspisChecks" in containing-log form. Next:
1. M7, the actual-run identification on the rows agent's 40-row run;
2. the clean-event copies (`CheckedAcceptance40`, `fibre_checks`);
3. then PayoutBound (9.3), statements first.

## 8. M1–M3 and M6: the merged in-place slot, its budget and the recovery (COMPILED)

Four modules in docs/research/future-version/lean/, compiled on the build host
against the L187 objects with Lean 4.32.0. Each ran in its own scope (MemoryHigh
6G, MemoryMax 8G, MemorySwapMax 0, TasksMax 64, 180 s limit). Kind of result: model
definitions and model theorems in R1's stored-proof and binary commitment model.
None is a source refinement or a composed security theorem. Every `#print
axioms` is a subset of `[propext, Classical.choice, Quot.sound]`. There is no
`sorry`, `axiom`, `native_decide` or raised heartbeats, and no warnings in the
final compiles.

| Attempt | Module | sha256 (source) | Exit | Wall | Peak RSS (time -v) | cgroup peak | Swaps |
|---|---|---|---|---|---|---|---|
| PSE-01 | AspisOneTxSummedLayout | 081883a4…4927b9 | 0 | 3.20 s | 4.22 GB | 0.44 GB | 0 |
| PSE-02 | AspisOneTxMergedSlot | 22d342ec…be22149 | 0 | 3.84 s | 4.23 GB | 0.44 GB | 0 |
| PSE-03 | AspisOneTxMergedBudget (first version) | 960590879…e9e351 | 1 | 3.19 s | 4.21 GB | 0.43 GB | 0 |
| PSE-04 | AspisOneTxMergedBudget | 72d277dc…2527f | 0 | 2.62 s | 4.24 GB | 0.45 GB | 0 |
| PSE-05 | AspisOneTxMergedRecovery | 3cbbf64e…2cd029f | 0 | 3.72 s | 4.22 GB | 0.43 GB | 0 |

PSE-03 failed in its last step, `mergedAll_budget`: `omega` saw
`short (mergedPrograms p q)` and its unfolded list as different terms. The fix
unfolds `mergedPrograms` in the goal as well as in the hypothesis. It is not a
mathematical change, and the same commit removed a redundant lemma and an unused
simp argument. "Peak RSS" includes the mapped L187 objects; the cgroup peak is
the scope's charged memory. Source revision: these four files are untracked on
`future-version` at 96c5cf266de; the local hashes equal the compiled ones.

### 8.1 The construction: R1's slot program with four constants made parameters

R1's frozen-order slot program (OraclePortFrozenOrderSlot.lean) is
`verifySlot_frozen p q batch kind`. It hashes every leaf of
`sortedPositions q batch kind` (`hashLeaves`, rejecting an unequal duplicate
digest at once). It then checks well-formedness (`wellFormed`: nonempty,
**length ≤ 16**, strictly increasing, below 2^18), the node count against
**`capacity (3*batch+kind)`**, and zero padding of the slot at
**`slotStart (3*batch+kind)`**. Finally it runs `runLevels 18` (in place, level
by level). The four constants in bold are the only parts specific to R1's
two-batch split. `AspisOneTx.slotB n cap start ps` is the same program with
`n`, `cap`, `start` and the position list `ps` as parameters. `hashLeaves`,
`runLevels`, `nodeCount`, `committedRoot`, `leaf` and `index` are R1's
definitions, used unchanged.

- **R1 instance.** `r1_slot_instance` proves `verifySlot_frozen p q batch kind =
  slotB 16 (capacity (3*batch+kind)) (slotStart (3*batch+kind)) (sortedPositions
  q batch kind) p q kind` by `rfl`. R1's slot program is literally an instance,
  so every generic theorem below is also a theorem about R1's slot. This is how
  the R1 checks are obtained.
- **Aspis merged slot.** `verifyMerged p q kind := slotB 22 (mergedCapacity kind)
  (mergedStart kind) (sortedAll q kind) p q kind`, where:
  - `sortedAll` is all 22 positions in R1's key order (index, then position),
    the order of `merged_keys`;
  - `mergedCapacity` is 296/296/254 (`SLOT_NODES`, fused.rs:724);
  - `mergedStart` is 28359 plus the earlier slots.

  `verifyMergedAll` short-circuits the three trees in the order C1, C2, folded,
  as `merged_merkle` does (fused.rs:800-806).

### 8.2 Statements next to the R1 statements they copy

**M1, layout (AspisOneTxSummedLayout).**

| Aspis | R1 | Difference |
|---|---|---|
| `acceptsSummed proof`: length 55815, magic `[65,83,80,73,83,0,0,2]`, byte 8 = 2, bytes 9..15 zero | `OraclePortHeader.accepts`: length 57607, magic `R1P3CB18` | length and magic only |
| `parseSummed b` | `OraclePortCompactDraft.parse b` | `acceptsSummed` in place of `accepts`; `scan` and `semanticRows` unchanged (they read only below 28359) |
| `parseSummed_header : parseSummed b = some p → acceptsSummed b = true ∧ p.wire = b` | `parse_header` | same proof |
| `parsedSummed_length : … → p.wire.length = 55815` | `OraclePortStoredWidthsC4.parsed_length` (57607) | number |
| `opening_fields_summed` (six widths 480/128/32/32/128/32 of opening `pos < 22`) | `OraclePortStoredWidthsC4.opening_fields` | same statement, summed parser |
| `mergedStart_values` (28359, 37831, 47303), `certificateStart_eq` (55431), `summed_total` (55431 + 384 = 55815), `merged_slot_within` | `OraclePortSelectedDraft.capacity`/`slotStart` (146/146/128/172/172/150 from 28359) | three slots in place of six |

**M2, path (AspisOneTxMergedSlot).**

| Aspis (generic, then merged) | R1 | Difference |
|---|---|---|
| `inPlaceB_success n`, `inPlaceB_path n` | `inPlace_success`, `inPlace_path` | bound `n` in place of 16; same proof |
| `slotB_path n cap start ps … (member : pos ∈ ps) (accepted : (eval H (slotB …)).2 = true) : ∃ path : Path (BinMultiproof.slots 18 (index q kind pos)), foldPath H path (H (leaf p kind pos)) = committedRoot p kind ∧ ∀ a ∈ fullTrace H path (leaf p kind pos), Read (eval H (slotB …)).1 a` | `slot_path … (member : pos ∈ batchPositions batch)` | membership in `ps` in place of `batchPositions batch`; conclusion identical |
| `r1_slot_path_check`: R1's `slot_path`, exact statement, re-derived from `slotB_path` | — | check |
| `slotB_recovery_at_index n cap start ps … : recoverAt tag width (cut tr frame) (slots 18 (index q kind pos)) (committedRoot p kind) = some (packed, salt)`, hypotheses `consistent`, `contains`, `bound : firstReads emptyTable tr ≤ Q`, `clean : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q) …`, `frameRead`, `rootRead`, `leafBytes`, widths | `OraclePortFrozenOrder.recovery_at_index` | the slot program only; same hypotheses, same exceptional event, same conclusion |
| `r1_recovery_at_index_check`: R1's `recovery_at_index`, exact statement, re-derived | — | check |
| `merged_recovery_at_index … (posBound : pos < 22) (accepted : (eval H (verifyMerged p q kind)).2 = true) …` | as above | every position `< 22` is in the single slot |

**M3, budget (AspisOneTxMergedBudget).**

| Aspis | R1 | Difference |
|---|---|---|
| `inPlaceB_bound n` : `… .length + 1 ≤ live.length + nodes.length / 32` | `OraclePortFrozen2Resource.inPlace` | bound `n`; same proof via R1's `levels` |
| `tailB_bound_strict` (`0 < cap`) : `… + 1 ≤ live.length + cap` | `OraclePortFrozen2Resource.tail` | parameters |
| `slotB_bound` : `(eval H (slotB n cap start ps p q kind)).1.length + 1 ≤ 2*ps.length + cap` | `OraclePortFrozen2Resource.slot` (`2*(batchPositions batch).length + capacity …`) | parameters; via R1's `leaves_bound` |
| `r1_slot_bound_check`: R1's `slot`, exact statement, re-derived | — | check |
| `merged_bound` : `+ 1 ≤ 44 + mergedCapacity kind`; `merged_bound_values`: ≤ 339, 339, 297 | R1 batch bounds 477 (= 165+165+147), 563 (= 195+195+173) | 22 positions, merged capacities |
| `short_length`: a short-circuited list issues at most the sum of its members' calls | inline in R1's `OraclePortFrozen2.batch_bound` | generic |
| **`mergedAll_budget : (eval H (verifyMergedAll p q)).1.length ≤ 975`**, for every H, p, q | `batch0_bound` ≤ 477, `batch1_bound` ≤ 563 | three slots, one transaction; no checkpoint term |

**M6, recovery (AspisOneTxMergedRecovery).**

| Aspis | R1 | Difference |
|---|---|---|
| `short_accepted`, `short_read` (any short-circuited list) | `OraclePortFrozenOrder.slots_accepted`, `slots_read` (for `slotPrograms p q ss`) | generalised to any list |
| `leaf_fields_summed` | `OraclePortAllSelectedRecoveryC6.leaf_fields` | `parseSummed` |
| **`authenticated_merged`** (below) | **`OraclePortFrozenOrder.authenticated`** (OraclePortFrozenOrderSelectedRecovery.lean:49) | `short (slotPrograms p q slots)` → `verifyMergedAll p q`; `parse` → `parseSummed`; `batchOf` removed. Conclusion, objects and exceptional event identical |
| `no_second_opening_merged` | — (corollary) | two accepted merged runs in one clean log, same root, same index ⇒ same payload |

```lean
theorem authenticated_merged (H : Bytes → State) (stored : Bytes) (p : Parsed)
    (parsed : parseSummed stored = some p) (q : Fin 22 → Fin 262144)
    (accepted : (eval H (verifyMergedAll p q)).2 = true)
    (log : List (Bytes × State)) (Q : Nat)
    (consistent : ∀ a ∈ log, a.2 = H a.1)
    (contains : ∀ a, Read (eval H (verifyMergedAll p q)).1 a → Read log a)
    (bound : firstReads emptyTable log ≤ Q)
    (clean : ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
      BinRawByteCollisionTargets.pred Q) emptyTable log)
    (kind : Nat) (kindBound : kind < 3) (frame : Bytes) (j : Fin 5)
    (frameRead : Read log frame)
    (rootRead : BinRawByteCollisionTargets.pred j frame = some (committedRoot p kind)) :
    ∀ pos, pos < 22 → recovered log frame p kind (index q kind pos) =
      some (OraclePortPackedChoiceC4.payload p kind pos)
```

On the R1 check for M6: R1's `authenticated` is about six slots and the Aspis
theorem about three, so neither is an instance of the other. Its single-slot
core, `recovery_at_index`, is re-derived exactly (`r1_recovery_at_index_check`),
and the remaining step is the same five-line proof in both.

### 8.3 Relation to the pair-binding agent's merged-multiproof theorems

`AspisPairResidual.Merkle.{merged_member_recovery, merged_query_recovery,
no_second_opening}` prove the same conclusion,
`recoverAt tag width (cut tr frame) (slots depth i) root = some (packed, salt)`,
under the same exceptional event at the same budget. They reach it by a different
route: their hypothesis is `BinMultiproof.Accept H root depth active v nodes trace`,
an abstract level-at-a-time acceptance relation, and they go through
`BinMultiproof.accepted_path`. The theorems here start from acceptance of a
concrete oracle program (`verifyMerged`, R1's in-place slot program with merged
constants) and go through R1's `slot_path` route (`levels_path`,
`leaves_retained`). That is the route of `OraclePortFrozenOrder.authenticated`,
which R1's bound uses. Both routes end in `recover_at_first_commitment`.

- **Supersede?** For the acceptance chain, yes. The Aspis copies of
  `OraclePortFrozenOrderChecks.accepted_checks` and its consumers (M9) take
  `authenticated_merged`, because the model decision's Merkle part is the slot
  program, not `BinMultiproof.Accept`. Their files are not edited and stay
  correct as theorems about `BinMultiproof.Accept`.
- **Reused?** No. Nothing here imports `AspisPairResidualMerkle`.
- **Same conclusion?** Yes, by the route the bound uses.
  `no_second_opening_merged` is the slot-program form of their
  `no_second_opening`.

Linking the two, by showing that an accepted `verifyMerged` gives
`BinMultiproof.Accept`, is not needed and was not done.

### 8.4 Counts: what is proved and what is still paper

| Count | Status |
|---|---|
| 339 / 339 / 297 per merged tree (2·22 + cap − 1) | PROVED (`merged_bound_values`), all inputs |
| 975 for the three merged multiproofs (66 leaves + ≤ 909 parents) | PROVED (`mergedAll_budget`), all inputs, rejections included |
| R1's per-slot formula | re-derived from the generic proof (`r1_slot_bound_check`) |
| 136 for the 40-row sampler prefix (115 + 21) | PAPER; needs PSD's 40-row sampler and a copy of `OracleDecisionPrereqSampler` |
| 1,111 for the Aspis model verifier (head) | PAPER; needs the 136 and the Aspis decision M5 (Merkle part 975 plus no other digest) |
| 1,112 (devnet source) | PAPER |

A consequence for M5: R1's `OraclePortExperiment.Budget` is the decision budget
1,046. The merged Merkle part, 975, fits under it. If the Aspis decision issues
no other digest (it has no checkpoint), the R1 constant 1,046, and with a 136
sampler prefix the envelope 1,161, remain valid upper bounds. That still has to
be proved for M5.

### 8.5 What is not established by these four modules

- **Source refinement.** That `merged_tree`, `verify_counting_merged` and
  `merkle_verdict` compute `verifyMerged`. In particular, the Rust well-formedness
  bound (`MAX_MERGED = 22`) has to match `wellFormedB 22`, and the
  duplicate-leaf rule (fused.rs:783-787) has to match `hashLeaves`. This is
  source refinement, as R1's slot program is for R1's batch trees.
- **Canonical scan.** That `parse_shape_summed` and `canonical_scan` compute
  `acceptsSummed` and `scan`.
- **Roots and reached run (M7).** That the three roots are read from the frames
  of rows 0, 2 and 30 of the 40-row run. This is `targets`, item M7.
- **Rest of the chain.** M4, M5 and M7–M9.

Nothing here touches the verifier, the prover or anything published. No
compute-unit, adversary, metric, failure-event or trust change is involved.

## 9. M5, M4 and M8: the Aspis decision, the typed batched check and accepted ⇒ AspisChecks (COMPILED); M7 open; scope of PayoutBound

Two modules, with the same compile set-up as section 8. Kind of result: model
definitions and model theorems in R1's stored-decision and binary commitment
model. None is a source refinement, a composed security theorem, or connected
to the release artifacts. Every `#print axioms` is a subset of `[propext,
Classical.choice, Quot.sound]`. There is no `sorry`, `axiom`, `native_decide` or
raised heartbeats, and no warnings in the final compiles. Local hashes equal
the compiled ones. The files are untracked on `future-version`.

| Attempt | Module | sha256 (source) | Exit | Wall | Peak RSS | cgroup peak | Swaps |
|---|---|---|---|---|---|---|---|
| PSE-06 | AspisOneTxDecision (first version) | e8e9e8fe…ff7473 | 1 | 5.00 s | 4.22 GB | 0.44 GB | 0 |
| PSE-07 | AspisOneTxDecision | b1a127e1…b0aea7 | 0 | 6.02 s | 4.24 GB | 0.44 GB | 0 |
| PSE-08, -09, -12, -13 | AspisOneTxChecks (versions) | ce032acd…, 481095e6…, 2f5d85f0…, f5071f10… | 1 | 20.8–39.6 s | ≤ 4.24 GB | ≤ 0.45 GB | 0 |
| PSE-10 | AspisOneTxProbe (probe, scratch) | 8d00b43d738a171bb103365bc0bef5b25c88e8fe6b65ab8e567f542f5536dd0c | 1 | 20.5 s | 4.21 GB | 0.42 GB | 0 |
| PSE-11 | AspisOneTxProbe2 (probe, scratch) | 6dfb5ce3…7814f | 0 | 7.11 s | 4.23 GB | 0.44 GB | 0 |
| PSE-14 | AspisOneTxChecks (without admission) | aa4cc657066b95e42b1999deaa170868b9307597654973a5d20a703c5c00b308 | 0 | 13.2 s | 4.26 GB | 0.47 GB | 0 |
| PSE-15 | AspisOneTxChecks (admission, first version) | 983aa21e…1643c2d | 1 | 10.9 s | 4.24 GB | 0.45 GB | 0 |
| PSE-16 | AspisOneTxChecks | 1f26406e…2f04d2 | 0 | 12.1 s | 4.26 GB | 0.46 GB | 0 |

**Failures, and what changed (none is a mathematical change).**
- PSE-06: two `rfl` placeholders where a named hypothesis was needed.
- PSE-08 to PSE-13: heartbeat timeouts in `isDefEq`/`whnf`. Each one occurred
  where a concrete replacement word, or a concrete field tower, met a defeq
  check: through a `let`, through `Iff.rfl` on `Boundaries`, or through `exact`
  after unfolding `FirstBatch`. This is the acceptance-link agent's lesson.
  - Probes PSE-10 and PSE-11 isolated it: projection lemmas `(withWords d W V).x
    = d.x` are instant by `rfl`, and `Iff.rfl` on `Boundaries` times out even
    after unfolding.
  - The fix restates every word-replacement fact by rewriting with those
    projection lemmas (`bnd_ww`, `fin_ww`). It moves the transport into
    `transport_core` over abstract words `W`, `V`, and states the `FirstBatch`
    congruence generically in the fields (`firstBatch_congr`), as R1's
    `HchecksAccumulator` does.
- PSE-15: a missing classical `Decidable` instance in the admission section.
- The probe files are mine, in lean-src and lean-out on the host and in the
  session scratchpad. They are not part of the deliverable.

### 9.1 Statements next to the R1 statements they copy

**M5, decision (AspisOneTxDecision).**

| Aspis | R1 | Difference |
|---|---|---|
| `dV_aspis : OraclePortStoredExperimentC4.Decision` | `OraclePortFrozenOrder.dV_frozen` (not the two-transaction `dV_frozen2`) | guard `Guard (take33 tr) ∧ tr.rounds.length = 40`; parser `parseReachedS` (`parseSummed`, R1's `Aligned` on `take33 tr`, plus `AlignedCert`: rounds 34..39 are the stored certificate frames); queries `queries (take33 tr)`; Merkle part `verifyMergedAll` (section 8) in place of `short (slotPrograms p q slots)`; arithmetic `arithmeticS` (R1's `input` on `take33 tr`, then `verifyS` on the 40 typed rows) |
| `accepted_detailsS` | `OraclePortFrozenOrder.accepted_details` | same shape, plus `length = 40` |
| `decision_budgetS : (eval H (dV_aspis stored tr m)).1.length ≤ 975` | `OraclePortFrozen2.decision_budget` (≤ 1,046 = 477 + 563 + 6) | merged slots, no checkpoint |
| `decision_budget_r1 : OraclePortStoredExperimentC4.Budget dV_aspis` | — | R1's 1,046 bound holds as a corollary |
| `admitted_aspis : admitS (dV_aspis s) = dV_aspis s`, `accepted_guardS` (in AspisOneTxChecks) | `OraclePortFrozen2Consumer.admitted_dV`, `OraclePortAdmission.accepted_guard` | `admitS` checks R1's guard on the first 33 rounds and length 40. **R1's `OraclePortAdmission.admit` cannot be used for Aspis**: its `Schedule` requires exactly 33 rounds, so it rejects every 40-round prefix. The Aspis clean event must use `admitS` |

Order: the model runs rows 0–39, then the terminal decision. Inside the
decision, the Merkle programs are the only oracle calls. The arithmetic
(`arithmeticS`) issues none, so its position relative to the Merkle check
inside the decision does not matter. Nothing here assumed the devnet build's
order. The Rust at the branch head (4045ecbdda3) runs the merged Merkle
authentication last, after the final sumcheck, which is the model's order. The
devnet build (8a4059c8bc2) ran it before rows 33–39.

**M4, typed batched check (AspisOneTxDecision).**

| Aspis `verifyS rs i` (decided Prop; reads on `rs.take 33` are R1's) | R1 `D0TypedChecks.verify rs i` |
|---|---|
| `LiteralMatchingData.read (rs.take 33) = some data`, `data = i.data` | same, on 33 rows |
| `Boundaries data` (the two boundary conjuncts) | `LiteralPairingChecks.checks rs` (three conjuncts; the first, `pair = claim`, is removed) |
| — | `R16DecisionQueryModel.verify` (per-query first fold, through R1's checkpoint model): **removed** |
| `EquationEndpoint i.decoded (rs.take 33) data` | same |
| `∀ q, decode = some q → FirstBatch eK (rhoOf i.rho) data q ∧ FinalPart rs data q (rhoOf i.rho)` | `∀ q, decode = some q → ClosedSum eK data q (rhoOf i.rho)`: **replaced** |

`FinalPart` holds exactly the acceptance link's rows-33..39 fields: `m33`,
`lamV`, `entry33`, `decode33`, `claimDef`, `rhs2Def`, `rounds`, `roundsLen`,
`entryRound` and `finalCheck`, all at the codec `decodePairS`. That codec is
the acceptance link's `decodePair` parameter, fixed here. It decodes the 64-byte
payload of a 64-byte frame (`AspisRows40.Protocol.payloadOf`) as two wide-field
values with R1's `SelectedFieldSequenceCodec.decodeWide`.
- **Canonical:** `decodePairS_canonical` shows a successful read determines the
  payload bytes as `encodeWide` of the values, so non-canonical encodings
  are rejected.
- **Untouched by word enrichment:** `decodePairS_enrich`.
- **Rust correspondence, OPEN (source refinement):** that `E::from_le_bytes` is
  `FoldedLeafCodec.decodeWide`, the same correspondence R1 needs for its folded
  leaf values.

The row-33 message deserves a note. The Rust does not store it: it computes
`claim` and `rhs2` and absorbs `claims_bytes(claim, rhs2)`. The model has the
prover supply row 33, and the decision accepts only if `decodePairS m33 =
some (claimS, rhs2)` with `claimS` and `rhs2` the computed values. Because the
codec is canonical, that fixes `m33`'s payload to the bytes the Rust absorbs.

**M8, selected checks and the containing-log theorem (AspisOneTxChecks).**

| Aspis | R1 | Difference |
|---|---|---|
| `SelChecks pub rs` | `OraclePortSelectedConsumerC6.Checks` | 40 rounds, R1's reads on `rs.take 33`. `writer` and `backend` are replaced by `boundaries`, `firstBatch` and `final : FinalPart`; `semantic` is R1's field on `observe` |
| `ofTypedS` | `OraclePortObservationTransportC6.ofTyped` | from `verifyS` |
| `transportS` (via `transport_core`) | `OraclePortObservationTransportC6.transport` | same three agreement premises. Semantic part: R1's `observe_withWords` and `OraclePortMatchingRewordC6.semantic`. First fold: PSC's `pair_withWords`. Rows 33..39: `decodePairS_enrich` and the map form of `reword` |
| `toAspisChecks : SelChecks pub rs → Nonempty (AspisChecks decodePairS pub rs)` | `OraclePortSelectedConsumerC6.toLiteral_nonempty` | target is the acceptance link's `AspisChecks` |
| `accepted_checks_aspis` (below) | `OraclePortFrozenOrderChecks.accepted_checks` | `dV_aspis`, `verifyMergedAll`, `authenticated_merged`; conclusion `AspisChecks decodePairS` |

```lean
theorem accepted_checks_aspis (H : Bytes → State) (stored : Bytes)
    (tr : ErasedPrefix) (m : ErasedMessage) (p : Parsed) (q : Fin 22 → Fin 262144)
    (parsed : parseReachedS stored tr = some p) (query : queries (take33 tr) = some q)
    (accepted : (eval H (dV_aspis stored tr m)).2 = true)
    (log : List (Bytes × State)) (Q : Nat) (consistent : ∀ a ∈ log, a.2 = H a.1)
    (contains : ∀ a, Read (eval H (verifyMergedAll p q)).1 a → Read log a)
    (bound : firstReads emptyTable log ≤ Q)
    (clean : ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
      BinRawByteCollisionTargets.pred Q) emptyTable log)
    (frames : Fin 3 → Bytes) (selectors : Fin 3 → Fin 5)
    (frameRead : ∀ k, Read log (frames k))
    (rootRead : ∀ k, BinRawByteCollisionTargets.pred (selectors k) (frames k) =
      some (committedRoot p k.val)) :
    Nonempty (AspisChecks decodePairS tr.statement
      (reword (OraclePortFrozenOrderChecks.maps log frames p) (typedRows p q tr)))
```

This is "accepted ⇒ AspisChecks" in R1's containing-log form. The checks are
on the typed rows carrying the words recovered from the log. Its hypotheses are
R1's (log consistent with H, Merkle reads in the log, first reads ≤ Q, R1's
single collision event, root frames read), and its conclusion is the
acceptance link's structure. With PSA's `aspis_checks_noHit_r1_checks` and
`aspis_relation` it reaches R1's spend relation on a no-hit transcript. That
composition is not written as one theorem here.

### 9.2 What is still open in this layer

**Update:** M7 and the clean-event hypothesis (M9) are done; see section 10.
The list below is kept as written.

- **M7, the actual-run identification.** This means instantiating
  `accepted_checks_aspis` at the actual 40-row run, which needs copies of:
  - `OraclePortFrozen2Reached.{accepted, slots_read, consistent, distinct_bound,
    frame_read}` and `OraclePortFrozen2Roots.targets` (the three roots read from
    the sampler frames of rows 0, 2 and 30), on the rows agent's
    `AspisRec40.Decision.original D dV_aspis P`;
  - `OraclePortFrozen2ActualChecks.maps_eq_builder` (recovered maps =
    `wordsFromRun`).

  R1 proves these with 33-row lemmas (`OraclePortStoredProjectionC4.frame_eq`,
  `OraclePortReplay.sampler_reads`, `OraclePortParsedRootsC6.{c2_record,
  folded_record}`). The roots part reads only rows 0, 2 and 30, so it should
  copy through `take33`. The frame and replay lemmas need the rows agent's
  40-row run. `distinct_bound` is the rows agent's `projected_first_reads`
  (Q + 1111). Not started in this round, because the run definitions it needs
  landed during it.
- **Clean event and consumer.** `CheckedAcceptance40` and `fibre_checks`
  (copies of `OraclePortFrozen2CanonicalChecks`, `OraclePortFrozen2C6` and
  `OraclePortFrozen2Consumer.fibre_checks`) come after M7. The admission
  property they use is `admitted_aspis` (9.1).
- **Source refinement**, outside this layer: that `verify_summed_format` at the
  branch head computes `dV_aspis`. In particular `fold_sums`' `lhs1 = rhs1` is
  `FirstBatch`, `finish_relation_round` gives `Boundaries` and `claimDef`,
  `sums.rhs2` is `rhs2Def`, `summed_final_checks` is `FinalPart`,
  `merged_merkle` is `verifyMergedAll`, and the codec is as above.

### 9.3 Scope of PayoutBound (form (B) of section 1.2a; statements only, not built)

**The join to prove.** For an accepted withdrawal:
1. The Pool's request bytes are the bytes the verifier is called with.
2. The verifier's entry rebuilds the statement from those request bytes and the
   authenticated accounts. That statement's PIN2 public bytes (pool ‖ deployment
   domain ‖ has-destination ‖ destination) seed the transcript of the accepted
   proof.
3. The Pool's transfer moves `amount` from the vault of that pool and deployment
   to that `destination_token_account`.

The proof is bound to the statement by the transcript seed, so 1–3 put the
payment's destination, pool and domain under the proof.

**Source-level statements needed (all OPEN).**
- **E1, entry.** At r1_pool_adapter_owned.rs, the one-transaction block of
  `stage2_owned`, `validate_asq8`, `authenticate_asq8_accounts` and
  `reconstruct_asq8_statement` (r1_pool_adapter.rs): the statement passed to
  `verify_summed_format` is `reconstruct(decode(request), authenticated
  accounts, candidate prefix)`. Its `semantic_public().public_bytes()` carries
  `request.public`'s pool, deployment domain and destination
  (pair_forest_semantic_terminal.rs:2020-2090). The emitted result is a function
  of that statement (`emit_result`).
- **P1, Pool request to verifier (made precise, lead 2026-11-11).** On the
  deployed route (`dispatch_pair_forest_terminal_readonly_v1` →
  `plan_pair_forest_terminal_dispatch_v1`):
  - The Pool decodes `r := decode(request_bytes)` (pair_forest.rs:1642-1643).
  - It pays from `r.public` (pair_forest.rs around :1700).
  - It calls the verifier with `data := encode(r)` (pair_forest_dispatch.rs:157,
    :342). The original bytes are not forwarded on this route. The route that
    forwards the exact original 1,880 bytes is audit-only, behind
    `pair-forest-full-asf8-audit` (pair_forest.rs:1843-1903).
  - The verifier decodes `data` again (`validate_asq8`) and builds the statement
    from `decode(encode(r))`.

  So the obligation is **decode ∘ encode = id on the encoder's image**:
  `∀ r b, encode r = ok b → decode b = ok r`, for
  `encode_pool_v1_pair_forest_terminal_request_v1` and
  `decode_pool_v1_pair_forest_terminal_request_v1`
  (crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs:432, :466). It is
  not encode ∘ decode = id: the original request bytes need not equal their
  re-encoding, and the proof is never checked against them.
- **P2, Pool payout.** The withdrawal plan
  (`plan_legacy_withdrawal_transfer_from_identity_v1`, vault.rs:387; called
  from pair_forest.rs around :1700 with `public.destination_token_account` and
  `public.amount` of the same decoded request) does three things:
  - it refuses unless the passed destination account is that key (vault.rs:454)
    and the vault is the Pool vault of the master named in the request;
  - it invokes `TransferChecked` with that amount (vault.rs:~505);
  - `validate_exact_withdrawal_delta_v1` (vault.rs:551) checks the vault and
    destination balances after the call.

  Nothing else in the transaction moves tokens out of the vault.
- **P3, result admission.** The Pool admits the payout only after reading the
  verifier's result and validating it against the request
  (`validate_authenticated_terminal_result_v1`, pair_forest.rs around :1750).

**R1 Pool settlement models: reuse or realise.**

| Model | Content (read) | For Aspis |
|---|---|---|
| `NGK_NFO_ReadModel.run` | The Pool's read of the verifier's return data: CPI result, program check, 792 bytes, decode | **reusable** if the Pool's read path is unchanged at the Aspis Pool pin (to check) |
| `NGK_NFR_CSettlement.run` | Post-verifier settlement cut: validate, lane, encode. Lane images are arbitrary. **No token transfer** | **reusable as the frame**; needs an extension with the withdrawal transfer (P2) |
| `NIB_ReadToSettlement.read_to_settlement` | Model composition emit → read → settle under `RuntimeReturnData`: `authenticated.value = ResultAdmission.value s` | **reusable** (one CPI, no checkpoint); it ties the Pool's admitted value to the verifier's emitted statement `s` |
| `NGP_L159.{History_statement, Carrier_statement, L159_statement}` | Two-transaction history (adjacent transactions, checkpoint copy, 1,768 saved bytes) and the TX1/TX2 carrier equality, or E_rec | **not reusable** (two-transaction). For Aspis, R1's `History_statement` disappears. The carrier part is replaced by E1 + P1, with no hash step: the same request bytes in one transaction |

None of them includes the token transfer or the destination. The result the
verifier emits (`PoolV1PairForestTerminalResultV1`: transition kind, master,
lane, output lane, nullifier, afterstate) does not carry the destination or
amount. So the destination join cannot go through the return data. It must go
through P1: the Pool pays from the same request it sends to the verifier.

**Trust row for the token transfer: NARROWED (lead's decision 2026-11-11; supersedes the wider text below, which is kept for the record).**

Why it narrows: the Pool checks the payout itself, around the call.
- **Before the call** (vault.rs:387-540) it requires:
  - the five account keys: mint = the pool's asset mint; vault = the pool's
    vault PDA; destination = the statement's destination key (vault.rs:454);
    authority = the vault-authority PDA; token program =
    `LEGACY_SPL_TOKEN_PROGRAM_ID`, executable;
  - parses of the mint, vault and destination token accounts, and their mints;
  - vault authority = the PDA, and no delegate, close authority or native flag
    on the vault;
  - `vault_after = vault.amount − amount` and
    `destination_after = destination.amount + amount`, overflow-checked.
- **After the call** (`validate_exact_withdrawal_delta_v1`, vault.rs:551-580),
  before the Pool persists any state, it re-reads the same five keys and both
  token accounts. It requires vault and destination mint = the plan's mint,
  vault authority = the plan's authority, `vault.amount = vault_after` and
  `destination.amount = destination_after`.

So the token-balance effect that PayoutBound states (exactly `amount` from the
pool's vault to the statement's destination token account) is checked by the
Pool's own reads. It is not assumed of the token program.

**What is still assumed, in its narrowest correct form:**
- **(R-a) Post-call visibility, runtime class.** After a cross-program invoke
  returns Ok, the account data the caller reads through its `AccountInfo`s is
  the data as the callee left it.
- **(R-b) Writable set, runtime class.** A cross-program invoke can change only
  accounts passed to it as writable. Here those are the vault and the
  destination (`AccountMeta::new` at vault.rs:~508-511); mint and authority are
  passed read-only. So no other account's token balance can move in this call.
- **No assumption about SPL Token's behaviour is needed for PayoutBound.** If
  the call does anything other than the exact transfer, either the Pool's
  re-read rejects (the transaction fails) or the two balances moved exactly as
  stated.

**What the delta check does not cover (residual, not needed for PayoutBound):**
- the vault's delegate, close authority and frozen state after the call;
- the destination's owner, delegate and state after the call;
- lamports of either account.

The vault fields matter for **custody** of the remaining vault funds, which is
a separate property (AGENTS.md section 1). A custody claim would need either:
- the SPL-specific assumption "TransferChecked, at the pinned program id, does
  not change the vault's delegate, close authority or state"; or
- an extended post-call check in the Pool. That is a code change, so it is an
  owner decision: compute units.

The destination's fields are not part of PayoutBound as stated ("to the
statement's destination token account"). The Pool does not check them before
the call either.

**Does the narrowing hold in every case?** Yes for PayoutBound, on the reading
above. The only case it does not cover is custody, which the wider row did not
fully cover either: it said nothing about delegates. R-a is the one assumption
not already implied by the wider row's reading. It replaces "the token program
debits and credits as documented", so the trade is a runtime-class
data-visibility fact in place of a program-behaviour fact. The lead's call on
whether that counts as "strictly less trust" for the report to the owner.

**Wider row as first proposed (superseded by the above, kept for the record).**
- **Name:** `SplTokenTransferChecked` (pinned SPL Token program id
  `LEGACY_SPL_TOKEN_PROGRAM_ID`, pinned version).
- **Statement:** an invoke of `TransferChecked { source, mint, destination,
  authority, amount, decimals }` by the Pool, signed for the vault authority PDA,
  that returns Ok has exactly these effects:
  - it debits `amount` from `source`'s token balance;
  - it credits `amount` to `destination`'s token balance;
  - it changes no other account's token balance, owner or mint.

  It returns an error, with no effect, when `source`'s balance is below
  `amount`, the mints differ, `decimals` is wrong, or `authority` is not
  `source`'s owner.
- **Nothing more is assumed:** no fee and no hook behaviour, and nothing about
  any other instruction.
- **Possible narrowing (for the lead, not decided).** The Pool re-reads both
  balances after the call and checks the exact deltas (vault.rs:551). So the
  two-balance effect is checked by the Pool's own reads, assuming post-CPI
  account data is the post-state, which is runtime-class. The row could then be
  reduced to "no other account changes". Narrowing a row is the owner's call.

**How the conjunct joins the rest of the outcome.**
1. `Runs1.trace` already associates the Pool's actions with the recorded
   actions.
2. E1 and P1 give: statement verified = statement rebuilt from the Pool's
   request.
3. The outcome's public object (form (A)) is that statement.
4. P2 plus the trust row give: payment = (request.amount → request.destination).

Together these give PayoutBound against the same public object, with no new
probabilistic event. The only probabilistic content stays in the existing
failure event (the proof bound to that public object).

**Size and hardest item (estimate).** About 6–10 model and source-statement
files:
- E1 statement and its extraction target (1–2);
- P1 and P2 statements over an extracted Pool payout path (2–3, needing the
  Pool payout functions extracted at the Aspis pin);
- the trust-row structure (1);
- extensions of `NGK_NFR_CSettlement` and `NIB_ReadToSettlement` with the
  transfer (1–2);
- the conjunct and its composition into the one-phase headline (1–2).

**Hardest item: P1 + P2 as source statements on the actual Pool code.** They
require extraction of the Pool's request split, codec round trip, withdrawal
plan and CPI. R1 never extracted the payout path: none of R1's models contains
the transfer. P1's codec round trip (re-encoding the decoded request) is the
precise point where a mismatch would let the verifier and the Pool see
different destinations.

## 10. M7 and M9: accepted ⇒ AspisChecks on the actual 40-row run, and the clean event's hypothesis (COMPILED)

Two modules, with the same compile set-up as section 8. Kind of result: model
theorems in R1's stored-decision and binary commitment model. They are not
source refinements, and no two-transaction module is imported. Every `#print
axioms` is a subset of `[propext, Classical.choice, Quot.sound]`. There is no
`sorry`, `axiom`, `native_decide` or raised heartbeats, and no warnings in the
final compiles. Local hashes equal the compiled ones. The files are untracked.

| Attempt | Module | sha256 (source) | Exit | Wall | Peak RSS | cgroup peak | Swaps |
|---|---|---|---|---|---|---|---|
| PSE-17 | AspisOneTxRun (first version) | 779a48de…69b800 | 1 | 4.35 s | 4.24 GB | 0.44 GB | 0 |
| PSE-18 | AspisOneTxRun | 86a13f1e…742bfa8b | 0 | 8.20 s | 4.26 GB | 0.45 GB | 0 |
| PSE-19 to PSE-22 | AspisOneTxCheckedAcceptance (versions) | 4308103a…, 6c723bc6…, 6cca8e18…, cfb4f0fa… | 1 | 4.5–66.7 s | ≤ 4.22 GB | ≤ 0.43 GB | 0 |
| PSE-23 | AspisOneTxCheckedAcceptance | cf5d5b2c22d7f49ba6ee02e6a802effffcf54e74ea6929f3fa7f4a220297383b | 0 | 4.66 s | 4.25 GB | 0.44 GB | 0 |

**Failures, and what changed (none is a mathematical change).**
- PSE-17: a missing import, an `omega` goal with two forms of the same log, and
  a local irreducibility attribute that blocked an R1 `change`. Each was fixed
  by scoping or restating.
- PSE-19 to PSE-22: an ambiguous identifier (`input`), and whnf timeouts. Lean
  evaluated the 40-round transcript while elaborating `rounds[n]'bound` and
  `statement`. The fix is R1's own `Frozen2CanonicalChecks` attribute (local
  irreducible `LiteralByteProtocol.protocol`, `LiteralByteSampler.samp`,
  `FS2.Protocol.transcript`), plus the row identity restated over abstract
  public input and proof (`ok_gen`).

### 10.1 M7 (AspisOneTxRun), next to R1

| Aspis (run `run40 D P H := eval H (AspisRec40.HitMass.original D dV_aspis P)`) | R1 | Difference |
|---|---|---|
| `reached_take33 : take33 (reached40 D P H) = OraclePortReachedRunC6.reached D P H` | — | the 40-row reached prefix's first 33 rounds ARE R1's reached prefix on the same proof (`AspisRows40.Literal.transcript_take33`); this is what lets R1's 33-round lemmas apply unchanged |
| `accepted40`, `decision_read40`, `slots_read40`, `consistent40` | `OraclePortFrozen2Reached.{accepted, decision_read, slots_read, consistent}` | 40-row verifier evaluation (`AspisRec40.Decision.verifier_eval`); the merged Merkle program |
| `distinct_bound40 : firstReads emptyTable (run40 D P H).1 ≤ Q+1111` | `distinct_bound` (Q + 1161) | from the rows agent's `verifier_issued` (≤ 1,111 per verifier call) |
| `chain_reads40`, `transcript_eq_of_chains`, `frame_eq40` (n ≤ 40), `frame_read40` (row < 40) | `OraclePortStoredProjectionC4.frame_eq`, `OraclePortReplay.frameFromView_eq`, `RawCutWordsFromView.frame_read`, `OracleProgramReplay.transcript_eq_of_agrees` | re-proved for rows below 40, from the 40-row verifier's evaluation and `Protocol.chain_eq`. The agreement hypothesis is stated on the chains' reads, not on R1's 33-row verifier |
| `targets40` | `OraclePortFrozen2Roots.targets` (body as `OraclePortReachedRootsC6.targets`) | `accepted_detailsS`, `parsedS` and `verifyS_accepted` in place of R1's; then R1's `erased_index`, `ParsedRootsC6` and `FrameShapesC6` lemmas on R1's reached prefix (through `reached_take33`) |
| `maps_eq_builder40` | `OraclePortFrozen2ActualChecks.maps_eq_builder` | the 40-row run's frames |
| `accepted_checks40` | `OraclePortFrozen2ActualChecks.accepted_checks` | conclusion `AspisChecks decodePairS` on `reword (wordsFromRun D (view run40)) (typedRows p q (reached40 D P H))`; collision event at `Q + 1111` |

### 10.2 M9 (AspisOneTxCheckedAcceptance), next to R1

| Aspis | R1 | Difference |
|---|---|---|
| `verifier_enrich40`, `recorded_eval40`, `original_view40`, `recorded_view40`, `original_fixed40`, `annotated_fixed40` | `OraclePortStoredExperimentC4.{verifier_enrich, recorded_eval}`, `OraclePortStoredProjectionC4.{original_view, recorded_view}`, `OraclePortStoredReductionC7.{original_fixed, annotated_fixed}` | 40-row experiment |
| `canonical_valid40` | `OraclePortFrozen2CanonicalChecks.canonical_valid` | from `accepted_detailsS` and `reached_take33`. Uses `message_idem` (R1's canonical retagging is idempotent) because the guard is read on the canonical run directly |
| `rows_gen`, `ok_gen`, `rows_eq40` | `OraclePortRowsCanonicalC6.rows`, `OraclePortFrozen2CanonicalChecks.rows_eq` | R1's `rows` takes `LiteralTranscript.valid` on every row, but `valid` admits payload rows only below 33. Rows 33..39 use `restore_canon_late` instead, which holds because the canonical retagging never produces a `.c2` or `.second` message at rows ≥ 33 |
| `accepted_checks_canon40` | `OraclePortFrozen2CanonicalChecks.accepted_checks` | `AspisChecks` on `rows40` (the recorded run's 40 rows) |
| `CheckedAcceptanceC4_40`, `original_clean40`, `checked_acceptance40` | `OraclePortStoredChecksC4.CheckedAcceptance`, `OraclePortFrozen2C6.{original_clean, checked_acceptance}` | 40 rows, `dV_aspis`, `Q + 1111` |
| **`fibre_checks40 D s P Q hq : AspisRec40.CleanStatement.CheckedAcceptance40 D (dV_aspis s) (pairProver s P) (Q+1111)`** | `OraclePortFrozen2Consumer.fibre_checks` | **exactly the rows agent's hypothesis `hchecks`**, discharged |

### 10.3 Against the rows agent's list (RECORDED-EXPERIMENT-40.md section 7)

Every item it named is supplied, in the shape named:

| Item | Supplied by |
|---|---|
| `parsed`, `query`, `accepted` | `accepted_detailsS`, `accepted40` |
| run trace as `log`, `consistent`, `contains` | `(run40 D P H).1`, `consistent40`, `slots_read40` |
| `frameRead` | `frame_read40` |
| `frames` = the first cells of rows 0, 2, 30, with `rootRead` | `frames40`, `targets40` |
| `maps_eq_builder` to the recorded rows | `maps_eq_builder40`, then `rows_eq40` to `rows40` (= `compiledRows40` through `annotated_fixed40`) |
| `bound` | `distinct_bound40` (from the rows agent's `verifier_issued`) |
| `clean` | `original_clean40`, from `CheckedAcceptance40`'s own no-collision hypothesis |
| the hypothesis itself | `fibre_checks40` |

Nothing could not be supplied. Two things the clean event's copies need, which
this file does not provide:
1. the admission identity is `admitted_aspis` (`admitS`), not R1's `admit`
   (section 9.1);
2. the clean event needs the format and tag facts (`format40`, `tag40`, rows
   agent's list) on `AspisChecks`. Those are the rows agent's copies.

### 10.4 What remains in this layer

- PayoutBound (9.3): statements next.
- Source refinement of `dV_aspis`, the entry and the Pool path, outside this
  layer.

### 10.5 Review of b39cfdd5d57 (soundness lead's reviewer, 2026-11-11)

Verdict, from the source only: faithful to R1's route, with caveats.

What the reviewer confirmed:
- `CheckedAcceptance40` has the shape of R1's
  `OraclePortConsumer.CheckedAcceptance` with 33 rows replaced by 40 and R1's
  checks by `AspisChecks decodePairS`.
- `fibre_checks40` has the binders, the one hypothesis `hq` and the proof steps
  of R1's `OraclePortFrozen2Consumer.fibre_checks`, with the Aspis decision and
  1,111 in place of 1,161. `pairProver` is R1's own constant.
- `dV_aspis` follows R1's `dV_frozen` on the first 33 rows and adds a
  length-40 check and the tie of rows 34 to 39 to the certificate bytes.
- The adversary is the same: any stored proof, any prover with `hq`, pointwise
  in the oracle. `Q + 1111` is derived (`distinct_bound40`, from `hq` and the
  verifier's 136 + 975 calls), and agrees with the collision event of the
  assembled bound.
- No `sorry`, axiom, `opaque`, `native_decide` or raised limit in the two files
  or their 13 dependencies. R1's tree is unchanged.

Caveats, each recorded as it stands:
- **Admission is not a conservative extension of R1's.** `admitS` and R1's
  `admit` accept disjoint sets, because R1's schedule requires exactly 33
  rounds. `fibre_checks40` does not use `admitS`. But the clean event's
  decoding completeness for rows 33 to 39 cannot be obtained from admission.
  It has to come from the shapes of those rows as the decision and the checks
  constrain them (64-byte payload frame, canonical decoding, the certificate
  tie). This was passed to the clean-event work the same day.
- **Rows 33 to 39 have no validity predicate on this path.** The `late`
  condition holds for every canonical prover, so it constrains nothing. That
  is correct here: R1 uses validity only for the restoration identity, and
  `rows_gen` takes that identity directly. `valid40` (AspisRows40Literal) is
  defined and not used on this path.
- **Scope.** Model level only: nothing ties `dV_aspis` to the Rust
  `verify_summed_format`. The statement is for a fixed stored proof; the
  40-row counterpart of R1's selection step (`annotated_selected`) is not
  committed, and neither is the clean event that consumes `fibre_checks40`.
- **Stale header.** `AspisOneTxMergedBudget.lean` still labels 136 and 1,111
  "PAPER" in its header, though both are now proved. The header is corrected
  at the coherent rebuild before the freeze, not now: changing the file
  changes its hash under the modules already compiled against it.
- **One line changed after the review.** `AspisOneTxRun.lean:107` used
  `VerifierCallBudget.firstReads_le_length`, a generic lemma that lives in a
  two-transaction module. It now uses the re-proved
  `AspisRec40.CallBudget.firstReads_le_length`. Nothing else in the file
  changed. New source sha256
  26cbb3f61f10a5f6a4c14aae485cb90549c482013947d8b5c03591c03d60ec97, host
  attempt LDJ-02; the modules above it were recompiled (ASPIS-FAILURE-BOUND.md
  section 7). The reviewer read the file before this change.
- **Mistyped hash.** The PSE-23 row carried a wrong tail. Fixed, with five
  others found by `tools/check_note_hashes.py` (RECORDED-EXPERIMENT-40.md
  section 5.5).

## 11. PayoutBound: the conjunct over a model of the Pool's withdrawal step (COMPILED, model level)

One module, `lean/AspisPayoutModel.lean`, namespace `AspisPayout`. It has no
imports: the model is self-contained. Kind of result: **model theorems about an
explicit model written in this file**. They are not a source refinement. That
the Rust computes the model is stated below as open obligations. Nothing here is
established for the deployed code.

| Attempt | sha256 (source) | Exit | Wall | Peak RSS | cgroup peak | Swaps |
|---|---|---|---|---|---|---|
| PSF-01 | 766c5b31…bf82d | 1 | 0.51 s | 0.49 GB | 0.08 GB | 0 |
| PSF-02 | d044b50d…f0fb8 | 1 | 0.58 s | 0.49 GB | 0.08 GB | 0 |
| PSF-03 | fa09391f…7c2f | 1 | 0.67 s | 0.49 GB | 0.08 GB | 0 |
| PSF-04 | b08da063…cccf61 | 0 | 0.75 s | 0.50 GB | 0.09 GB | 0 |
| PSF-05 | 54f0fed9f1faf2a7ea38412842050416c6b7fac15af51d8ee3e84e7eb121180f | 0 | 1.83 s | 0.49 GB | 0.08 GB | 0 |

**Correction at PSF-05 (lead's review, 2026-11-11).** The theorem compiled at
PSF-04 was vacuous. Its hypothesis `e1` ended with
`q.deployment = ids.deploymentOf q.pool` under `∀ q`, that is, for every
request. A request can name any deployment, so no such hypothesis holds, and a
theorem with a hypothesis that cannot hold says nothing. The check that
rejects a wrong deployment is made by the entry on the statement it accepts,
so the condition belongs on accepted statements only. PSF-05 moves it to a
separate hypothesis `e1d : ∀ s, accepted s → s.deployment = ids.deploymentOf s.pool`.
The conclusion is unchanged. Two theorems were added so that this cannot
recur unnoticed:
- `Witness.first_e1_form_unsatisfiable` keeps the counterexample to the first
  form (pool 0 with deployment 0, against a pool whose deployment is 4).
- `Witness.instance_paid` builds one concrete instance (addresses are
  numbers, the callee does the exact transfer) in which every hypothesis of
  `payout_bound` holds, and applies the theorem to it. It shows the
  hypotheses can hold together. It is not evidence about the deployed
  programs.

The hashes of PSF-01 to PSF-04 agree with the hashes the host recorded when
it compiled them (first line of each receipt's `stdout.log`).

PSF-01 to PSF-03 failed on `match` terms that needed `dsimp only` after a
rewrite, and on two `rfl`s where named hypotheses were needed. None is a
mathematical change. Every `#print axioms` is `[propext, Classical.choice,
Quot.sound]`; Lean prints `Classical.choice` as `choice` because the file opens
`Classical`. There is no `sorry`, `axiom`, `native_decide` or raised heartbeats,
and no warnings. The local hash equals the compiled one.

### 11.1 The model

Each step mirrors the Rust:
- `decode`: the Pool decodes the request.
- `plan ids r keys w0` (vault.rs:387-540) rejects unless:
  - the amount is nonzero;
  - the destination key is the request's destination;
  - the vault, vault authority and mint are those of the request's pool
    (`PoolIds`);
  - the pre-call vault and destination token accounts parse, with the plan's
    mint, and the vault authority is the plan's;
  - the amount is at most the vault balance.

  It computes `vaultAfter = vault − amount` and `destAfter = dest + amount`.
- The cross-program call is `callee : World → World`, an **arbitrary** state
  change. The model puts no constraint on it.
- `DeltaOk` (vault.rs:551-580): on what the Pool reads after the call (`read`),
  both accounts parse, both mints are the plan's, the vault authority is the
  plan's, and the balances equal `vaultAfter` and `destAfter`.
- `step` returns the post-call state if the plan and `DeltaOk` hold, and
  `none` otherwise (the transaction fails).

Token accounts carry `mint`, `authority`, `amount`, and `rest` for every field
the Pool does not read: delegate, close authority, frozen state, lamports.

### 11.2 The two trust rows (runtime class, accepted by the lead under the owner's 2026-11-04 rule; to be reported to the owner)

- **R-a, post-call visibility (`RowA`).** After a cross-program invoke returns
  Ok, the account data the caller reads through its `AccountInfo`s is the data
  as the callee left it. Used for the vault and the destination, the two
  accounts the Pool re-reads.
- **R-b, writable set (`RowB`).** A cross-program invoke changes only the
  accounts passed to it as writable. Here those are the vault and the
  destination (`AccountMeta::new`, vault.rs around :508-511); mint and
  authority are passed read-only.

No other row is used. Nothing about the token program's behaviour is assumed.

### 11.3 Statements proved (model level)

```lean
theorem step_paid (ids) (r) (keys) (w0 w1) (callee read)
    (rowA : RowA keys callee read w0) (rowB : RowB keys callee w0)
    (ok : step ids r keys w0 callee read = some w1) :
    Paid ids r keys w0 w1
```

`Paid` says:
- `0 < amount`;
- destination key = the request's destination;
- vault key = the vault of the request's pool;
- vault ≠ destination;
- the vault balance after the call plus `amount` = the vault balance before,
  with the pool's mint;
- the destination balance after = before plus `amount`, with the pool's mint;
- every other account is unchanged.

```lean
theorem payout_bound (ids) (encode decode) (stmtOf) (accepted) (r) (keys) (w0 w1) (callee read)
    (rowA : RowA keys callee read w0) (rowB : RowB keys callee w0)            -- trust rows
    (p1 : ∀ q b, encode q = some b → decode b = some q)                       -- OPEN obligation
    (e1 : ∀ q, (stmtOf q).pool = q.pool ∧ (stmtOf q).deployment = q.deployment ∧
      (stmtOf q).destination = (if q.withdrawal then some q.destination else none) ∧
      (stmtOf q).amount = q.amount)                                           -- OPEN obligation
    (e1d : ∀ s, accepted s → s.deployment = ids.deploymentOf s.pool)          -- OPEN obligation
    (p3 : ∃ b q', encode r = some b ∧ decode b = some q' ∧ accepted (stmtOf q'))  -- OPEN obligation
    (p2 : step ids r keys w0 callee read = some w1)                           -- OPEN obligation
    (withdrawal : r.withdrawal = true) :
    ∃ s, accepted s ∧ s.destination = some keys.dest ∧ keys.vault = ids.vaultOf s.pool ∧
      s.deployment = ids.deploymentOf s.pool ∧ Paid ids r keys w0 w1 ∧ s.amount = r.amount
```

In words: if the Pool's withdrawal step returns Ok, then the statement `s`
satisfies four things:
- the verifier accepted a proof bound to `s`;
- exactly `s.amount` left the vault of `s`'s pool;
- that amount arrived at `s`'s destination token account;
- `s`'s deployment is that pool's.

Nothing else changed.

### 11.4 Each hypothesis, labelled

| Hypothesis | What it is | Label | Where |
|---|---|---|---|
| `rowA` | post-call visibility | **trust row R-a** | runtime |
| `rowB` | writable set | **trust row R-b** | runtime |
| `p1` | decode after encode is the identity on the encoder's image | **open obligation** (Aspis's codec; never a trust row) | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs:432 (encode), :466 (decode) |
| `e1` | the verifier builds the statement it checks the proof against from the request it decoded, carrying that request's pool, deployment, destination (iff withdrawal) and amount | **open obligation** (source refinement of the entry) | r1_pool_adapter_owned.rs, one-transaction block of `stage2_owned`; `validate_asq8`, `authenticate_asq8_accounts`, `reconstruct_asq8_statement` (r1_pool_adapter.rs); `semantic_public().public_bytes()` (pair_forest_semantic_terminal.rs:2020-2090) |
| `e1d` | the entry accepts only a statement whose deployment is its pool's | **open obligation** (source refinement of the entry: `authenticate_asq8_accounts`) | r1_pool_adapter_owned.rs, one-transaction block of `stage2_owned`; `validate_asq8`, `authenticate_asq8_accounts`, `reconstruct_asq8_statement` (r1_pool_adapter.rs); `semantic_public().public_bytes()` (pair_forest_semantic_terminal.rs:2020-2090) |
| `p3` | the Pool sends the verifier `encode r` of the request it decoded, and pays only after the verifier accepted a proof bound to the statement built from those bytes | **open obligation** (source refinement of the Pool's call) | pair_forest.rs:1642-1643, pair_forest_dispatch.rs:157, :342; `validate_authenticated_terminal_result_v1` (pair_forest.rs around :1750) |
| `p2` | the Pool's payout path computes `step` on that same request, with the pool key used for the vault and authority addresses being the request's pool | **open obligation** (source refinement of the Pool's payout path) | vault.rs:387-580; pair_forest.rs around :1700 |

`p1` was not proved: proving it at model level would need a Lean model of the
1,880-byte request codec. Proving it for the Rust needs that codec extracted, or
a hand model plus its refinement. Neither exists. So it stays open, and that is
what it needs.

How `accepted` connects to the rest: it is the event "the verifier accepted a
proof bound to `s`". In the outcome conjunct (section 1.2a, form (B)) it is
instantiated by the one-phase run's acceptance, whose transcript is seeded with
`s`'s public bytes. That instantiation is part of composing PayoutBound into
`Outcome1` and is not written yet.

### 11.5 Attempts to break it

| Attack | Result | Rejected by |
|---|---|---|
| A destination account other than the statement's | the step returns `none` | the plan's key check (`wrong_destination_rejected`, proved); vault.rs:454 |
| The same account as vault and destination | no Ok step exists | the exact-delta check, which would need `v − amount = v + amount`, plus the nonzero-amount check (`same_account_rejected`, proved; `Paid.distinct`) |
| Amount 0 | the step returns `none` | the plan's nonzero check (`zero_amount_rejected`, proved); vault.rs:398 |
| A callee that moves tokens through a third account | no effect outside vault and destination | R-b (`Paid.others`); the vault and destination balances are exact by the delta check, so a detour through a third account cannot change the net |
| A callee that changes the vault's authority | no Ok step exists | the post-call authority check (`authority_change_rejected`, proved); vault.rs:575 |
| A callee that changes the vault's mint, or the destination's | no Ok step exists | the post-call mint checks (inside `step_paid`) |
| A callee that sets a delegate or close authority on the vault, or freezes it | **not rejected** | **gap, recorded**: these are in `rest`, which the Pool does not re-read. They do not affect PayoutBound, which concerns the two balances. They affect custody of the remaining vault funds, which stays open and outside PayoutBound. No Pool code change is proposed: it would raise compute units |
| A callee that changes the destination's owner, delegate or state | not rejected | outside PayoutBound as stated (payment to the destination token account). The Pool does not check these before the call either |
| The verifier sees a request different from the one the Pool pays on | excluded only through `p1` and `p3` | open obligations, stated |
| A transfer request (no destination) | no payout conjunct (`withdrawal` hypothesis) | the Pool plans no withdrawal for a transfer (pair_forest.rs, `withdrawal_plan` is `None`) |

### 11.6 What is open

- `p1`, `e1`, `e1d`, `p2`, `p3`: source obligations on Aspis's own code.
- Instantiating `accepted` with the one-phase run's acceptance, and conjoining
  PayoutBound into `Outcome1`.
- Custody of the remaining vault funds (the delegate, close-authority and
  frozen-state residual).
- Until all of the above are proved, the only claim made remains: "bound into
  the transcript and present in the public object; the relation does not
  constrain it".
