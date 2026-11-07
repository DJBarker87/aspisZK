# AMN: the minimal A1/A2 obligation and the cheapest sound plan

Target not yet established. This package closes no row and discharges no premise. It settles what the split-B top consumes from A1/A2 and replaces the NND_ brief. Base: `research` at ccce7a55d1e. Lean: `AMN_ReturnedPath.lean` and `AMN_Minimal.lean`, which import RSL_, TCK_WeakRoot0 and TAS_Interfaces only.

## 1. Where native1 and native2 occur, and what each occurrence needs

The top instantiates `native1 := model1` and `native2 := model2` (`AdapterRw...stage1_owned/stage2_owned (DrvC_Installation.sdk c)`). A1/A2 are consumed only by NNE_'s A3/A4/A5. In EVB `top_splitB_full` (lines 212-222), TFM `top_split` and TAS `top`, `a1` goes only to `a5.recorded` and `a3.accepted1`, and `a2` only to `a4.accepted2`. The headline binders that mention the natives are:

### 1.1 accepted1, accepted2

`S2W_D189Wrappers.first n1 copy allocator e1 id data1 state1 = ok (.Ok (saved,post1,final1))` and `second n2 allocator e2 id data2 slot state2 = ok (.Ok (post2,final2))`, one occurrence each. NNE_A3 and NNE_A4 derive these from the actual Ok run plus A1/A2. This needs only the **Ok direction** at the selected occurrence: actual Ok with bytes `saved` implies the model returns Ok `saved` (TX1), and actual Ok implies model Ok (TX2).

### 1.2 game (d), through CPP_Invocation.native

`CPG_RuntimeTrace.Step.invoke` uses only `(CPP_Invocation.native n1 n2 copy allocator id bank.cells (invocation bank input)).1` (the store) and `.2.1` (the event). The definition (lean/CPP_Invocation.lean):

```lean
def native ... (input : Invocation A) : Effect A :=
  match Hiq_ReleaseRoute.route input.call.data with
  | .first => firstEffect store input.call (first native1 copy allocator id store input)
  | .second => (store,.rollback,.inr (second native2 allocator id store input))
  | .reject => (store,.rollback,.inr (.ok (.Err .InvalidInstructionData)))
```

and (lean/Hir_Call.lean):

```lean
def firstEffect (store : Store) (call : Call A) (reply : FirstReply A) : Effect A :=
  match reply with
  | .ok (.Ok (saved,_,_)) => (commit store (call.layout.handles 2).1 saved, .committedWrite ..., .inl reply)
  | _ => (store,.rollback,.inl reply)
```

- **native2 is never inspected by game (d).** The `.second` arm's store and event are `store` and `.rollback` whatever the reply is. This is the fact TAS_WIRING section 1 already records.
- **native1 is inspected at every stage1-route invocation** in both `p.actions t` and `p.actions u`, including adversarial invocations that fail. The recorded physical event must equal the model's, so the model must commit exactly when the actual run returned Ok, and with the same `saved`. Two things follow. (i) Ok direction with exact bytes. (ii) If the actual run returned Err, the model reply must not be `.ok (.Ok _)`. The error value, payload, log line and event chronology are never read, because the `_` arm swallows them. NNE_Stage1Error already consumes only `∃ pe, ... = ok (.Err pe)`. A model `fail` would also roll back, so `≠ ok (.Ok _)` would be enough with a one-lemma NNE change.
- **Aborts are not an A1 obligation.** NNE_AbortRollback handles them by stamping the abort-indicator state `false` (ruling (bo)), so a stamped invocation cannot commit.

### 1.3 queries (L154) and the charged events

`queries : ∀ H, (ARW_Induced.issued native1 copy allocator id a H).length ≤ Q0+Q1`, where (lean/ARW_Induced.lean)

```lean
def issued (H) := let i := eval H a.first
  i.1 ++ match first native1 copy allocator i.2.entry id i.2.data i.2.state with
    | .ok (.Ok (saved,post,final)) => (eval H (a.second i.2 saved post final)).1
    | _ => []
```

This is a statement parameter (TAS `X.QueriesF fx`, supplied by `queries_mk := id`). It is a hypothesis about the adversary, so it imposes **no proof obligation on the actual code**. It counts the adversary's own queries only ("Native wrapper computation is pure here"). native1 enters only through the choice of whether phase-2 queries are counted. At worlds where the attack succeeds, A3 already gives model acceptance at that same first input (Realizes puts `i` into the context), so phase-2 queries are counted. Where the model accepts but the actual run rejects, the count only increases, which is conservative. No Err or abort direction is needed here. E_head and E_rec are definitions over `native1 := model1` (`P := ARW_Induced.program n1 ...`). The numeric bound is proved about them, and the actual-run inclusion is NNC_'s proved `root0_or_rec`. Neither imposes an A1/A2 obligation.

### 1.4 Caveat carried, not resolved here (RZ-STATE)

The abort path relies on NNE choosing each invocation's allocator state from the actual exit. TAS_TopB already escalates this as RZ-STATE. One could also delete A1's Err arm by stamping `false` on Err invocations, but that is **not** recommended: ruling (bo) defines the indicator as "an allocation fails exactly when the actual invocation aborted", and the change would make the model's input encode the actual outcome. It would need an owner ruling.

### 1.5 Conclusion

- **A2 needs only this:** at the selected TX2 occurrence, a returned-Ok arm of the canonical 241 reference (at an EnvRep environment, under Exhibited) implies that model2 returns `ok (.Ok ())`.
- **A1 needs only this:** for every 345 argument, a returned `Ok b` arm implies model1 returns `ok (.Ok saved)` with `nativeBytes saved = b`, and a returned `Err` arm implies model1 returns some Err.

NNE_AcceptanceSig.physical already defines ModelRet1/ModelRet2 exactly this way (ModelRet2 starts with `a = child2 ... → r = .ok () → ...`). The over-ask came from the TAS docstring and NND_AMENDMENT ("ModelRet ... for Ok AND Err", "complete AdapterRw native Result"). NND's both-arm, exact-payload 234 bridge goes beyond what any consumer reads.

## 2. The cheaper route

### 2.1 Fresh emissions are not part of A1/A2

A1/A2 say "returned arm of the frozen-source reference implies model outcome". They never mention `I`, the actual function. The actual code enters only through the RowSpec roots (`I.f ∈ Ref`), whose emission provenance is the actual side's concern (row jobs, lead note (bk)). The AdapterRw model is a definition inside the statement, not a claim about deployed code. So NND's E001/E002 extractions, the `NND_Registry.adopted` fresh-equals-historical replay, NND_FreshStage1/FreshFirstDecoded/FreshTx1Source and NND_TX1_REPLAY are **not needed** for A1/A2, although they remain valid support for the row jobs. One frozen-versus-model difference does matter, because the reference transcribes frozen source: frozen `require_zero` (suffix loop) against the model's index loop. NND L117 already proves this symbolically for arbitrary slices.

### 2.2 Compared routes

- **R0 (NND as briefed):** per-definition equality, fresh emission against AdapterRw, both arms, exact payloads, chronology. This is the most expensive route and is mostly not consumed.
- **R1 (the lead's suggestion):** the model satisfies the same RSL RowSpecs, and two functions satisfying one functional spec agree. Formalised as `AMN.transfer1/transfer2`, it needs (a) a model-side RowSpec proof for every OPEN row, (b) returned-determinism of every reference, and (c) **liveness**: the model returns wherever the reference can. RowSpec membership does not give (c), because an allocation site admits both the returned and the aborting observation (`AMN.alloc_admits_both`). Each row then needs a model-side membership proof plus a liveness lockstep, which is more work than R2. The ledger check found that most CLOSED child roots on these paths are already stated on the model: NFU_ZeroPort on `AdapterRw...require_zero`, NHS_CheckpointPacket on `VTop_Stages.Ops.op3/op4/op7 (DrvC_Dictionary.ops (F3V_Install.configuration c))`, and NMN_064.root on the VTop body. Every OPEN parent on the path is still OPEN, though (stage1_owned, stage2_owned, first_decoded, tx1, validate_asq8). So no model-side parent roots exist to reuse.
- **R2 (recommended): the NND_Returned shape, restricted to the consumed arms.** This has two halves. (a) A pure evaluator `val` with `Returns (Ref a) env (val a env)`, meaning every returned arm equals `val`. This is returned-determinism with an explicit value and needs no liveness, because the model is evaluated directly. (b) Model transport from the value only: `val = ok v → model Ok v` for TX2, plus `val = error _ → model Err` for TX1. Formalised as `AMN.viaReturns2/viaReturns1`, which yield `A2min`/`A1min`, and `toNND_A2/toNND_A1` then give the exact TAS fields. NND already built half (a): NND_LaneReturned (217), NND_RegistryEval (234), NND_AuthEval (233), NND_ValidateEval (242, parameterised by `NND_PoolValues.Values`), NND_Stage2Eval (241, parameterised by PoolValues and `NND_Tx2Values.Values`) and NND_Stage1RefEval (345, parameterised by `NND_Tx1ReturnedValues.Values`). What remains for (a) is instantiating those three Values parameters (leaf-law functionality). For (b), only the Ok path (TX2) or the Ok path plus one Err-class step per exit (TX1) is needed.
- **Slots the top inspects:** R2 needs facts about `DrvC_Installation.sdk c` slots only at the arguments reached on Ok paths (TX2) or returned paths (TX1), pointwise. No dictionary equality is needed. `NND_Missing.instance` must still be a definition, because Exhibited is a substitution, but its laws are needed pointwise only.

### 2.3 Necessary check (teeth)

`AMN.a1_forces_det` shows that the Ref-quantified A1 implies the reference's Ok arm is functional wherever the model is. If any library leaf law on a returned path is relational, meaning two Ok values at the same arguments and environment, A1 is unprovable as stated. The RSL gate already requires complete laws. The NND brief makes the leaf audit the first stage.

## 3. Minimal interface (compiled)

`AMN_Minimal.lean` (namespace `RSL.AMN`):

- `MinSig S`: `Ok1 : Ctx → TX1_345.Args → Bytes → Prop`, `NotOk1`, `Sel2 : Ctx → TX2_241.Args → Prop`, `Ok2`. The docstring gives the host terms from NNE_AcceptanceSig.physical.
- `withMin S M : Sig`: ModelRet built from MinSig. `ofNND_A1/ofNND_A2` and `toNND_A1/toNND_A2` show that at such a Sig the TAS fields **equal** `A1min/A2min`.
- `A1min`: `ok` (Ref returned `Ok b` → `Ok1 c a b`) and `err` (Ref returned `Err e` → `NotOk1 c a`), for all `a`, at EnvRep, under Exhibited.
- `A2min`: `ok` (Sel2 c a → Ref returned `Ok ()` → `Ok2 c a`).
- `modelRet2_error_vacuous`, `a1_forces_det`, `transfer1/2` (R1, with its liveness premise explicit) and `viaReturns1/2` (R2).

`AMN_ReturnedPath.lean` provides generic returned-path inversion lemmas for `Spec.bind`, `RS.bind` (Ok and Err), `seq`, `check`, `ofOption`, `ofExcept`, `ofCloned`, `index`, `lift` and `call`, plus `alloc_admits_both`. These are the one-time tool for the TX1 Err-class steps and for any row without an NND evaluator.

Validation: two single-file `lake env lean` compiles against a local RSL/TCK/TAS build (Lean v4.31.0, macOS, 24 GiB machine). Both exited 0, with peak RSS at most 421 MB, 0 swaps and under 2 s each (AMN_COMPILE.tsv). `#print axioms` lists only `propext` and `Quot.sound`, or none (AMN_AXIOMS_OUTPUT.txt). There is no sorry and no axiom declaration. There was no host run, package build or combined import. RSL/TCK/TAS were rebuilt locally from research sources first, all exit 0 with at most 729 MB.

## 4. Statement change (before and after, for the NND target)

- **Before** (NND_AMENDMENT): both TAS fields "for Ok AND Err", "complete AdapterRw native Result", "all adopted comparisons must use fresh frozen emissions".
- **After**: the exact TAS fields at NNE's physical Sig, which equal `A1min/A2min`. No quantifier, carrier, failure event or conclusion of the top changes. TAS_TopB and NNE are untouched, and the top's statement is identical. This weakens the *brief*, not the TAS field: the field at the physical Sig was already minimal. The remaining premises are satisfiable, since an Ok/Err-preserving model satisfies them, and they do not contain the conclusion.

Target not yet established.
