# NNH_ resume brief (run 5): one literal host, pointwise transports, one final consumer

Target not yet established. Read first: AGENTS.md; evidence/int-plan-20261107/INP_REPORT.md (the item-by-item diagnosis this brief implements); TAS_TopB.lean, TAS_Interfaces.lean, AMN_REPORT.md; your own NNH_REMAINING.md and NNH_ExactRemainingTypes.lean. Branch codex/cx-integrate-20261107, prefix NNH_, existing caps (MemoryHigh 6G, MemoryMax 8G, swap 0; Lean -M7000). The one 16 GiB scope is reserved for S8. Budget: 160 actual scopes, 0 Kani, 0 extraction. Commit at every step boundary; do not push.

## What changes from run 4

1. Do NOT write another conditional G0 over an arbitrary `Sbase : Sig`. Build the literal host Sig once (S2). Every later field is stated at that Sig, and only one final consumer exists (S8).
2. A1 and A2 do not wait for any row. They use only the RSL Ref (rev4) and the delivered canonical libraries. Only S8 waits for rows.
3. Use pointwise slot lemmas only. Whole-dictionary congruence, whole-function `rfl`-first dispatch and broad `simp` over concrete seven-account or full-buffer terms are banned (L454, L559, L570, L462 already failed). A failed shape is replaced by a different shape. Two failures of one shape class stop that shape.
4. Each step has a scope cap. At the cap, stop the step, write the exact open slot or lemma into NNH_REMAINING.md and move to the next independent step.

## Steps

**S0 (cap 2).** Compile NNH_ContinuationCombined with NNH_Stage1ZeroCurrent. NNH_Stage1ZeroOk and NNH_U64Bytes must not be in any import closure. No new export until S8.

**S1 preflight (cap 10). Report each item as pass/fail before S2.**
- P1: print `RSL.Env`. If its fields are exactly sha256/pda/clock/reservation, prove `NNH_HostEnv.EnvRep … env → env = environment …`.
- P2: state and prove A0 `digestSource` at the literal configuration (`op43 := LIB_Env.hashv (envOf c)`) against the headline `hashv`, `p1`, `syscall`. If it fails, stop and report the exact mismatch. Do not change op43 silently.
- P3: for `tx2Op11`, table every VTop slot that `tx2_common` reaches on the Ok path at `NNH_CorrectConfiguration.sdk`, and mark each `rfl` or needing a lemma. The expected lemma slots are geometry (against `NJC_ClosedCalls.geometry`), query (against `NHT_PacketOps.query NJJ_QueryOps.concrete 0 0`), merkle (against `NLP_NativeMerkle.action (H env)`, via `Op5T_Concrete.stage_source`) and finish (against `NLB_Parent.finish r`).
- P4: `rfl` check that `NNC_NMFB.root0_or_rec`'s event at `allocator := NNE_AbortIndicator.allocator`, `a := NNH_StateNormalize.normalize a`, `Q := Q0+Q1` is the `NNH_RecordedCharge.recorder` event.
- P5: recompile the NNH TX1 Returns chain (`NNH_ReturnsBundle.tx1_returns` and its inputs) against RSL rev4 (521d37fa6ed). Ref is unchanged; any statement break is a finding.

**S2 literal host (cap 16).**
- `NNH_HostCtx`: a structure over the headline binder block (TAS `Sig.Ctx` docstring) with `A := Bool`, `allocator := NNE_AbortIndicator.allocator`, `CoreError := NFN_NEW_GeometryDictionary.CE`.
- `missingLit c := NNH_Tx2Configuration.select (NNH_CorrectConfiguration.residual m0 (envOf c)) (envOf c)` for a fixed explicit inhabitant `m0`, and `Exhibited c := c.missing = missingLit c`.
- `S_host` on `NNH_HostEnv.install`, plus the NNE `Data`/`RecordSig.Data`.
- The literal `ExecB` (RZ-STATE): `build` is the constructor, `realizes_mk` comes from the NNH_StateNormalize eval-map lemma, `exhibited_mk := rfl`, `queries_mk := id`, `ERec fx H :=` the P4 recorder event, `eventRec_mk := Iff.rfl`.
- `Split`, `Headline`, `A0`, `R0Rep`.
- RecSig/RecSelect from `NNC_RecSelect.selects` + `NNH_StateSelect`.
- No field may be a hypothesis of this step's theorems except a representation predicate that is also proved non-vacuous here (TAS §5 step 8).

**S3 A2 (cap 18).** Prove `NNH_ExactRemainingTypes.tx2Op11` (under `Dom064 V0`, which contains Root0) by the converse of `Tx2N_Execution.common`: every canonical `NJJ_Common.run` step returned Ok, and each model slot equals the canonical call at those arguments (P3 table). Then compose `NNH_Stage2To064.source`, the op44/op53 tail (L596/L597), the 241 Returns evaluator and `AMN.viaReturns2` into `NND_A2 S_host …`. Only the selected Ok direction is in scope.

**S4 A1 (cap 55).** Work on the rev4 base. Install the `NNH_S1CodecOk` ports at op21/op24. Transport op10 (`current vops`) pointwise, child slot by child slot, against the canonical VL/P values on the returned path. Add the 328/345 glue and the P1880 discharge from the decoder length. For the Err arm, use an NNH_-prefixed copy of the NNE physical Sig whose ModelRet1 Err clause is `¬ ∃ x, model1 … = .ok (.Ok x)`, and an NNH_ copy of the NNE_Stage1Error consumer. No merged NNE module is edited. The result is `NND_A1 S_host …`. Record the Err-clause restatement before/after for the lead.

**S5 NMF_B (cap 30).** Produce `NNH_NMFPrime.Packet` at the host from Root0-free facts:
- `f`, `writerRoot` and `writerHeader` from `Accepted1` at the model (`ARU_FirstHeader.accepted`, `ARU_WriterReached.reached`, `NMF_WriterRoots.serialized`);
- `s`, `origin` and the TX2 half of `cuts` from the SAME native records (`NNH_Tx2ConcreteInputs.produce`, `NNH_EnvEntryWorld.native`, `NNH_WeakEntryNative.produce`) identified with the model reads of `e2.second secondSizes`;
- `persisted` from `game.checkpoint`, `p.copied t = saved` and RuntimePersistence.

`NMF_GameRoot` must not be used: it needs `accepted2`. Then apply `NNH_NMFPrime.assemble` with host-defined `Associated`, `rootImage` and `eventImage`, each closed by `rfl`/`Iff.rfl`. None may be a hypothesis.

**S6 HeadlineB (cap 12).** Prove `outcomeRec`, the Outcome with inner `bad := E_rec`, as EVB §2.3 describes: `FJv_DRelease.remove'` at the account recorder plus a `FJv_DNativeAccepted` copy. Heavy imports go on the build host under caps.

**S7 averaging (cap 4).** Prove `NNH_DeployedOuter`: for every `wOf` and `H`, `max (r H) (ind (Runs … ∧ ¬ OutcomeRec …)) ≤ m H + ind (E_rec H)`, from `TASB.fail_sub_rec` and `EVB.no_second_charge`. Pair it with `NNH_RecordedCharge.bound` and the existing `failureModel ≤ total (Q0+Q1)` chain at `a := normalize a`. Do not instantiate `TASB.Expect` on the fail indicator, and do not build a joint program that determines World: `wOf` is unrestricted. This reading of owner condition (5) goes to the lead.

**S8 final (cap 10; WAITS for row roots TX1:094/328/345 and TX2:233/242/241).** Write one consumer of `RSL.TASB.top_splitB` at `S_host` with the ledger27 CLOSED roots for 137/087/217/234 (replacing the candidate producers), the row roots, and S3 through S7. Then run the combined import in the 16 GiB scope, one raw axiom audit of the final root, non-vacuity, one manifest replay and the AGENTS §6 receipt.

## Forbidden in every final statement

Root0, Realizes, hash-injectivity, success, NativeRep/selected/rootImage/eventImage hypotheses; a constant adversary; any conditioning on Realizes; raised heartbeats, caps or timeouts; sorry/axiom; nonstandard axioms (bv_decide). Report "target not yet established" until S8 passes and the lead credits the top.
