# A12P: what A1/A2 really require, why rows do not compose, and the weakest plan

Target not yet established. This is a read-only audit. It closes no row, field or premise. One stand-in compiled in the scratchpad (section 7). Paths are relative to `evidence/` unless they start with `lean/`.

## 1. What the conditional top consumes (Q1)

`TAS_FinalB.deployed_splitB_conditional` (integrate-20261111/TAS_FinalB.lean:18-19,31) forwards `a1 a2` through `NNH_Run6Top` and `NNH_Run6Physical` (:44) into `NNT_TopL.top_splitB_physical` (g1b2-20261108/NNT_TopL.lean:68,78). `NNH_DeployedOuter` (NNH_DeployedOuter.lean:47-48,69) only forwards them. Inside the top, `a1` and `a2` are passed opaquely to three consumers and nowhere else:

| use | site | projection actually read |
|---|---|---|
| `a5.recorded c a1 …` | NNT_TopL.lean:43 | `a1.stage1` in NNH_Stage1View.lean:44 (`.1`, the **Ok** clause) and NNH_Stage1Error.lean:32 (`.2`, the **weak-Err** clause), at **every** stage1-route invocation in `p.actions t` and `p.actions u`, at any `env` with EnvRep |
| `a3.accepted1 c _ a1 …` | NNT_TopL.lean:46 | `a1.stage1 … .1 (d.saved c) rfl` (NNH_AcceptanceSig.lean:56): Ok clause at the selected TX1 occurrence, `env1` |
| `a4.accepted2 c _ a2 …` | NNT_TopL.lean:53 | `a2.stage2 … rfl rfl rfl` (NNH_AcceptanceSig.lean:70): Ok clause at the selected TX2 occurrence, `env2` |

The field types are TAS_Interfaces.lean:321-329. At `S_host` the stand-ins are NNH_AcceptanceSig.lean:31-41:

- `ModelRet2 c a r := a = child2 … (d.e2 c) … (S.env2 c).clock → r = .ok () → native2 (model2 c) … = ok (.Ok ())`. So **NND_A2 at S_host is already A2min**: Ok direction only, selected occurrence only.
- `ModelRet1 c a r := ∀ e p data, a = child1 d.err e p data → (Ok clause) ∧ (weak-Err clause ¬∃ saved, … = ok (.Ok saved))`. Both clauses are consumed. The Err clause is needed because game (d) inspects `native1` at every stage1 invocation (AMN_REPORT 1.2), including adversarial failing ones.

EnvRep (NNH_HostEnv.lean:14-18) fixes `sha256`, `pda`, `clock` and the reservation bit. So the `∀ env` in the fields ranges over `envOf c` only and adds no generality.

**Can the field type be split?** For A2, no: it is already minimal. For A1, `ModelRet1` is a conjunction, so the Ok and Err halves can be proved as two separate theorems and paired in a five-line constructor *without* changing any type. A field-type split (`a1ok`, `a1err`) would let `a3` consume `a1ok` first. The top still needs `a1err` for `a5`, so the split changes the landing order and closes nothing. **Recommendation: no field-type change.** Removing the Err clause would need the RZ-STATE allocator ruling (AMN 1.4). That is an owner matter and it is not recommended.

## 2. AdapterRw model against the emitted bodies (Q2)

**Parents: the same Rust, token-identical bodies, different Lean constants.**
- `model1 c = AdapterRw.r1_pool_adapter.owned.stage1_owned (NNH_CorrectConfiguration.sdk m0 (envOf c) …)`. This is a historical Aeneas extraction, closed over a ~50-slot `AdapterRw.Ops` dictionary built by `IDa_Deployed.seed`/`deployedConfiguration` (lean/IDa_Deployed.lean:81-101), FIq/FIp/DrvC installs and the NNH residual fill (NNH_CorrectConfiguration.lean:8-19).
- The row producer `NNG_TotalProducer345.producer` (tx1-principal-20261111/NNG_TotalProducer345.lean:12-16) is a port of `NMT_345.emitted` = `NMT_stage1_owned.r1_pool_adapter.owned.stage1_owned c.c0 … c.c16` (tx1-owned-20261111/NMT_345Context.lean:63-64). That is the fresh E001 extraction, with its own nominal inductives and 17 explicit callees, installed by `NNG_Calls345.calls env` (NNG_Calls345.lean:24-44).
- NND has already proved by `rfl` that the fresh frozen parents, rewritten into `Ops` slots, *are* the model bodies:
  - `NND_FreshStage1.source` (model-bridge-20261111/NND_FreshStage1.lean:451-453);
  - `NND_FreshFirstDecoded.source` (:20-23);
  - `NND_FreshTx1Source.source` (:115-118) for `verifier.candidate.tx1`;
  - NND_TX1_REPLAY.json records `token_equal: true`;
  - TX2 is the same except for the `require_zero` loop, which `NND L117` covers symbolically.
- The two sides are therefore **definitionally related at the parent level, modulo a nominal carrier map**. The carrier maps already exist: `mapOuter/mapCore` in NNG_Calls345, `toT3/fromT3/toT12` in NNG_Carriers094.

**Leaves: genuinely different Lean models of the same Rust.** The sdk installs V8-era natives. The rows and the library install the NL*/NJ*/LIBC/NKV natives:

| slot | model (sdk) | row/library side |
|---|---|---|
| Merkle batch | `Op5T_Install.body Port4B_Install.leaves …` (lean/Op5T_Concrete.lean:9-13,37-44; the **same body for TX1 `current` and TX2 `stage`**) | TX1: `LIBC_BatchMerkle.model = NLL_Parent.model (LIBC_CohortHash.H env)` (libc-20261111/LIBC_BatchMerkle.lean:27-30). TX2: `NLP_NativeMerkle.action (LIBB_PartitionEnv.H env)` = NKV `batch_merkle` (tx2-common-20261110/NLP_NativeMerkle.lean:11-14) |
| geometry | two SAQ_Constructor installs, then Port5Q1 terminal (NNH_HANDOFF:539-543) | `Port3_GeometryStage.geometry NFN_NEW_GeometryDictionary.adopted` |
| query | Tx1Q_SameCut / stage query install with SAQ_Decoder and FIp slots | `LIBC_QueryOps.ops`, `NJJ_Common.query` |
| finish/semantic | `IDa_Deployed.finish`/`boundaries` (FIo/FIn/SAG/Port3) | LIBC finish values (`NNH_FinishReturns.value`) |
| inactive decode | `Port1_LibrarySource.decode` (release overwrite) | `NJC_ClosedCalls.inactive` |
| TX2 064 | VTop `tx2_authenticated` at the installed stage | `NNH_064Install.f064` = NMN_064 native over `NJJ_Common`/`NLP_NativeMerkle` (integrate-20261111/NNH_064Execute.lean) |

The H functions also differ: `LIBB_PartitionEnv.H` repartitions with `LIBB_C04Partition.partition`, while `LIBC_CohortHash.H` uses `LIBC_HashPartitions.split`.

**Why the credited row roots cannot replace the leaf work.**
- RowSpecs are *soundness* statements: `∀ a env, Domain a → Ref a env (impl a env)` (rowspec-lead-20261107/RSL_TX1_345.lean:139-141). A1 and A2 need *completeness on the returned arm*: Ref returned r implies a model outcome.
- Going through a row would need (i) model ≈ producer at the leaves, which is the same pointwise work, and (ii) producer **liveness** wherever the Ref has a returned arm.
- (ii) is not available from the rows. `Spec.alloc` admits both `ret` and `abort` (rowspec-lead-20261107/RSL_Base.lean:195). The installed Impl is quantified over the allocation oracles `allocation217/allocation234/alloc1/alloc2` (NNH_Run6Installed.lean:7-30), so a credited producer may legitimately abort where the Ref returns.
- Rows help in one direction only. Given model ≈ producer, a model `Ok s` gives "producer returned `ok (bytes s)` ∈ Ref", and `tx1_returns` then gives the evaluator value, with no liveness needed. That is the weak-Err arm. It still needs the same leaf equalities, so it saves nothing over stepping directly against the evaluator.
- Conclusion: **compose at the parents (rfl replay plus carrier maps), work pointwise at the leaves, and state every leaf and body lemma as a full Result equality or an Ok-iff**, so that one pass yields both A1 arms (section 6).

## 3. Correctness point found by this audit (lead-visible, not an owner matter)

`AMN.viaReturns1/2` (a12-min-20261107/AMN_Minimal.lean:184-206) asks for `val = ok b → model ok b` for **all** arguments. `Returns` constrains nothing at `Spec.panic` sites or at off-domain `Spec.call` sites (RSL_Base.lean:201,223-224; `NND_Returned.panic`). At those sites the evaluator's value is a free "junk" choice, which no constraint ties to the code, and the model fails or runs on regardless.

So `NNH_ExactRemainingTypes.tx1Ok` / `NNH_HostA1Targets.ok` are **strictly stronger than A1**. They are false at any reachable panic or off-domain site whose junk value is `.ok _`, even though A1 holds there vacuously. The stand-in `A12P.okT_false` versus `A12P.a1_shape` (section 7) exhibits exactly this.

For the 345 top level the junk is `.ok []` (NNH_Stage1RefEval.lean:12). It is unreachable, because `badRoute` covers `length ≠ 3` (RSL_TX1_345.lean:82-83). The child evaluators (`NNH_Tx1Returns.values` for 328/094/087/136/137, and the 241 chain) have not been audited.

The fix is support-only and needs no RSL edit. Either prove each junk site unreachable on the reached path, or use `.error` junk. `.error` junk makes `okT` vacuous there and makes the weak-Err obligation true, because the model fails (`A12P.okT_errorJunk`, `errT_errorJunk`). Off-domain call sites need the domain derived on the reached path, which `NNH_Run5bA1Domain` already does for 328/094/087. Item X0/Y0 below makes this audit the first scope of each lane.

## 4. Classification of open items (Q3)

(a) = instantiation of a merged theorem; (b) = a genuine new lemma; (c) = blocked by an interface decision.

**NNV_REMAINING (A1):**
1. **Scan/semantic Verified (b).** Transport `NNH_FinishReturns.value` through the fixed `FinishModel.finish` at the same prefix, challenges and transcript, then associate the result with `LIBC_PreparedCarriers.verified`. The first unclosed goal, verbatim, is `NNH_ObservedReturns.value ⟨pub, LIB_Carriers.bytes bytes⟩ (envOf c) = .ok sem → (DrvC_Installation.currentInstalled (configuration c)).op9 (NNV_PreparedAtHost.digest c) (…toCurrentPublic pub) bytes () none = .ok (.Ok (NNV_PreparedInputs.sem sem))`. Reuse NNV_SemanticPrefix.returned and the NNH_ResultPortTransport.finish technique (L738). About 200-300 lines.
2. **Prepared front (b), after 1.** Compose 1 with NNV_PreparedNative.returned, NNV_PreparedDomainPorts and NNH_Run5bPreparedModel.source (L889, full Result against NGN_Emitted.prepared). About 100-150 lines.
3. **Continuations, split three ways.**
   - Query installation: (b), **shared with A2**. Generalise NNU_QueryLoop.source / NNU_Query.source (a2-20261108/NNU_Query.lean:21-37) from `NNH_Tx2SlotTransport.stage` to the current dictionary. About 100-200 lines.
   - Batch: (b), **shared with A2**; see section 5.
   - Flush/checkpoint: (b). Reuse NNV_CheckpointDigest/Value (L046/L047). About 100-200 lines.
4. **Common/afterstate getter diagram (b).** Reuse NNV_CommonAssociation and NNV_AfterstatePort. About 100 lines.
5. **328/345 composition (a) plus a small (b).** The parents are the rfl replays NND_FreshFirstDecoded.source and NND_FreshStage1.source. `require_zero` is NND L117 plus the 1768 checkpoint length. The codec slots op21/op24 are already NMT values (NNH_S1HostCodec, L800). What remains is bind-stepping. About 150-250 lines.
6. **Global weak Err: dissolves.** If items 1-5 and the 094 body are stated as Ok-iff or full Result equalities, the Err arm is the converse direction (`A12P.both_arms`). No separate pass is needed. Supersede it.
7. **Assembly (a).** `AMN.viaReturns1` plus `toNND_A1`, with `NNH_ReturnsBundle.tx1_returns` and NNV_WeakErrHost.modelRet1 (L049), after X0.

**NNU_REMAINING (A2), with the running continuation's state** (.worktrees/cx-a2/…/NNU_CONTINUATION.md, through L068):
- **Merkle parent bridge (b), shared** (section 5). Pointwise leaf/node/row-height (L042-L045) and the endpoint/wrapper/native pieces (L064-L067) are done. The parent is open.
- **Inactive slot: CLOSED at L052** (`NNU_Inactive.source/returned`, the global ∀-slice form). Nothing further is needed.
- **Common converse (b).** It has support: NNU_CommonCuts L063, CommonResume L066, CommonSelected L068. The source-ordered construction of the successful `tx2_common` is still open. About 150-300 lines.
- **tx2Op11 (a) once Merkle and common are done.** Assemble parse, common and Merkle against `NNH_ExactRemainingTypes.tx2Op11` (NNH_ExactRemainingTypes.lean:11-20). About 60-100 lines.
- **Composition (a).** `NNH_Stage2To064.source` (NNH_Stage2To064.lean:18-44), `NNU_Stage2Tail.returnedCuts` (CLOSED L061), op44/op53, `tx2_returns`, `AMN.viaReturns2` and `toNND_A2`, after Y0. About 80-150 lines.

**(c) items: none.** No open member needs an interface or owner decision. MultiproofConeP6Verify.verifyState_eq is not usable (it needs a total digest law and length ≤ 5504), but the pointwise route avoids it, so it is not a blocker.

## 5. Shared obstruction (AGENTS rule 7)

Both lanes call the **same** Merkle body, `Op5T_Install.body Port4B_Install.leaves D proof p.queries p.roots folded k hash`:

- TX1 at `k = 0`, through `Op5T_Concrete.current` (`ops.op6 … 0#usize`, NND_FreshTx1Source.lean:50-51);
- TX2 at `k = 1`, through `Op5T_Concrete.stage` (NNU_MerkleSlots.installed).

They compare it against two NKV-derived natives under two different H functions. NNU is building a TX2-only parent bridge, fixed at `.Two` and `LIBB_PartitionEnv.H` (NNU_MerkleVerify/MerkleTail). NNV left "batch call at SAME roots and digest" open. Geometry was proved twice already (NNV_CurrentGeometry L045, NNU_Geometry L015), and the query loop is about to be duplicated. The weakest fix is one parametric Merkle parent lemma that takes the node/leaf oracle agreement as an explicit argument, which each lane discharges for its own H, plus one generalised query-loop lemma.

## 6. Weakest sufficient plan (Q4)

**NNY_ (A2; continue inside the running NNU allowance, 12 scopes left, then a fresh cap of 20):**
- **Y0 (1 scope).** Junk audit of every `panic`/`call` discharge on the 241 Returns path at the selected occurrence (`NNH_Libraries.tx2_returns` chain). Prove unreachability or switch to an `.error`-junk copy. Changes support only.
- **Y1 `NNY_MerkleShared.parent` (4-8 scopes, about 150-300 lines).** Restate the open NNU bridge generically:
  ```lean
  theorem parent (H : Bytes → State) (D : VTop_Stages.aspis_core.digest.Digest32 Unit)
   (agree : NNY_MerkleShared.NodeLeaf D H)   -- definition: pointwise digest agreement on
                                              -- C04 node/leaf request shapes (NNU L042/L043 form)
   (proof : Slice U8) (p : VTop_Stages.verifier.Prepared) (folded : Array U8 32#usize)
   (k : Usize) (hk : k.val < 2) (q : ∀ j, j < 22 → p.queries.val[j]!.val < 262144) :
   NHT_ResultPort.action (NKV_FRef.verifier.candidate.batch_merkle (NKV_ConcreteChildren.ops H)
     (NKV_ConcreteChildren.digest H) proof p folded k ()) = .ok (.Ok ()) →
   Port4B_Install.batch D proof p folded k () = .ok (.Ok ())
  ```
  Here `agree` is a definition discharged per lane by theorems. It is never a top premise. Then derive the NNU_REMAINING statement verbatim at `H := LIBB_PartitionEnv.H env`, `k := 1`, with the `agree` instance from L038/L042/L043. Keep L042-L045 and L064-L067. Supersede only the `.Two`/LIBB-specific parent attempt.
- **Y2 common converse (6-10 scopes).** Keep the L063/L066/L068 route unchanged. Consume Y1, NNU_Geometry/Query/Offsets, NNU_Inactive and NNH_Run5bFinishEdge.selected.
- **Y3 `tx2Op11` (2-3 scopes)**, then **Y4 the A2 field (2-4 scopes)**, exactly as stated in section 4.

**NNX_ (A1; fresh job, cap 50):**
- **X0 (1-3 scopes).** The same junk audit over `NNH_Tx1Returns.values` (328/094/087/136/137). Domains on reached calls come from NNH_Run5bA1Domain and NNV_DecodeP1880.
- **X2 query (3-5 scopes).** Generalise NNU_QueryLoop.source over the dictionary and instantiate it at the current install. **Coordinate with NNY**: one generic lemma, two instances.
- **X3, then X4: finish/Verified, then prepared front (8-12 scopes).** Items 1-2, stated as full Result equalities on the reached path.
- **X5 flush/checkpoint (3-5)** and **X6 common/afterstate (2-4)**: items 3 and 4.
- **X1 Merkle TX1 (3-6, after Y1).**
  - Prove `NNY_MerkleShared.NodeLeaf (current digest) (LIBC_CohortHash.H env)` on C04 shapes.
  - Prove the link `LIBC_BatchMerkle.model ↔ NKV batch_merkle` at `k = 0`. Search the NLL_/LIBC_ modules first; if no such theorem exists, it is a new lemma of about 100 lines.
  - Instantiate Y1.
- **X7 094 body Ok-iff (4-6).** Rewrite with NND_FreshTx1Source.source (rfl), then bind-step with X1-X6:
  `currentInstalled.op10 … = ok (.Ok v) ↔ F.tx1 ⟨…⟩ env = .ok (bytes v)` on the reached domain.
- **X8 the 345 Ok-iff (3-5),** through NND_FreshFirstDecoded/FreshStage1.source and L117:
  ```lean
  ∀ missing env err reserve, NJC_FilledClause.reserved reserve = env.reservation →
   ∀ program xs data saved,
   r1_pool_adapter.owned.stage1_owned (NNH_CorrectConfiguration.sdk missing env err reserve) program xs data
     = .ok (.Ok saved) ↔
   NNH_ReturnsBundle.tx1Value ⟨key program, accounts xs, bytes data⟩ env = .ok (bytes saved.deref)
  ```
  The `←` direction is `tx1Ok`. The `→` direction gives the weak Err of `NNH_HostA1Targets.err` by contraposition, so item 6 is superseded.
- **X9 A1 field (1-2).** `AMN.viaReturns1` plus `toNND_A1` at `S_host`, via `child1` decomposition and NNV_WeakErrHost.

**Order and parallelism.** X0, X2-X6 and Y0-Y2 can run in parallel. Then X1 after Y1, X7, X8, X9 and Y3-Y4. One combined import at the end, then one axioms audit.

**Kept:** all 34 NNV accepted roots, all NNU L001-L068 passes, `NNH_Stage2To064`, `NNH_ReturnsBundle`, and the AMN interfaces.

**Superseded:**
- NNV item 6 as a separate pass;
- an A1-local batch proof;
- the TX2-only Merkle parent statement;
- any second, independent query-loop proof.

**Not needed:** fresh extraction, Kani, row re-proofs, a field-type change, or any RSL edit.

**Owner-visible points: none.** The field split is a lead decision, recommended against. The junk-value correction is support-level. The release target, the Err-arm requirement and the RowSpecs are unchanged.

## 7. Ready-to-paste Codex briefs

**NNY_ (A2).** Goal: the exact field `RSL.TAS.NND_A2 (AspisR1.NNH_Run5bHost.S_host L0 copy std) NNH_Libraries.L NNH_Libraries.D NNH_Libraries.V0`, with no added top premise and no Root0/Realizes/success/representation premise. Read evidence/a12-plan-20261108/A12P_REPORT.md sections 3-6 and NNU_CONTINUATION.md. Do these in order:
1. Y0: audit every Returns `panic`/`call` discharge on the selected 241 path and record each junk value. Prove unreachability, or use an `.error`-junk copy of the evaluator. Changes are support-only.
2. Y1: prove `NNY_MerkleShared.parent`, parametric in `H`, digest `D` and batch `k < 2`, with a pointwise node/leaf agreement *definition* discharged by theorems. Never take it as a hypothesis of a delivered field. Derive the NNU_REMAINING parent statement verbatim at `LIBB_PartitionEnv.H env`, `k = 1`. NNX_ will instantiate it at `LIBC_CohortHash.H env`, `k = 0`, so keep the statement lane-neutral.
3. Y2: finish the source-ordered common converse on the L063/L066/L068 route.
4. Y3: prove `NNH_ExactRemainingTypes.tx2Op11`.
5. Y4: assemble A2 with NNH_Stage2To064.source, NNU_Stage2Tail.returnedCuts, tx2_returns, AMN.viaReturns2 and toNND_A2.

Compile the smallest changed file first. No concrete buffer reduction, no unchanged rerun, no cap increase. Report "target not yet established" until A2 typechecks at S_host, with raw axioms standard-only.

**NNX_ (A1).** Goal: the exact field `RSL.TAS.NND_A1 (AspisR1.NNH_Run5bHost.S_host L0 copy std) NNH_Libraries.VL NNH_Libraries.P NNH_Libraries.C`. Read A12P_REPORT sections 1-6, NNV_REMAINING and NNV_HANDOFF. Reuse all NNV accepted roots. Do not re-prove parents: NND_FreshStage1/FreshFirstDecoded/FreshTx1Source.source are rfl replays of the model bodies. Do these in order:
1. X0: audit the junk values of `NNH_Tx1Returns.values`.
2. X2: generalise NNU_QueryLoop.source over the dictionary, sharing it with NNY_.
3. X3/X4: finish/Verified, then the prepared front, starting from NNV's first unclosed goal.
4. X5: flush/checkpoint. X6: common/afterstate.
5. X1: after NNY_MerkleShared.parent lands, prove LIBC node/leaf agreement and the LIBC_BatchMerkle-to-NKV link, then instantiate at k = 0.
6. X7: the 094 Ok-iff. X8: the 345 Ok-iff as stated in section 6.
7. X9: viaReturns1 and toNND_A1.

State every slot and body lemma as a full Result equality or an Ok-iff, so that the weak-Err arm follows by contraposition. Do not run a separate global Err pass. No field-type change, RSL edit, Kani or extraction. Compile the smallest file first; no unchanged rerun and no cap increase. "Target not yet established" until A1 typechecks at S_host with standard axioms.

## 8. Validation (this audit)

The stand-in is `/private/tmp/claude-501/-Users-dominic-ZK/3db59790-41f3-4c53-ae90-3fc42a8cab96/scratchpad/a12-plan/A12P_Teeth.lean`. It mirrors the RSL `Exit/Obs/Spec/panic` definitions and `Returns`, and proves `a1_shape`, `val_returns`, `okT_false`, `okT_errorJunk`, `errT_errorJunk` and `both_arms`.

- Command: `lean A12P_Teeth.lean` (core Lean, elan default toolchain on this Mac).
- Result: exit 0, wall 2.51 s, peak RSS 417 MB, 0 swaps.
- `#print axioms`: none for each printed theorem.

No host or build-host job ran. No project file other than this report was written. Nothing was staged or committed.

Target not yet established.
