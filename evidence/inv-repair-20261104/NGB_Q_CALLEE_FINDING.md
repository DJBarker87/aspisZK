# Q callee naming audit (inspection, no row-status ruling)

TX1:182 and TX2:108 remain CLOSED in the inherited NFX basis. TX1:168 remains OPEN. No status is changed by this audit. The 22 query conversions and one batched-accumulation conversion are compiler-confirmed in NGB_MIR_EDGES.json; their results are arguments to the non-prover no-op trace, so Rust evaluates them.

For accumulation, the complete model packet is NFS_NEV_AccumPacket.result_state_effects, in namespace NFS_NEV_AccumPacket, with `open Aeneas Aeneas.Std Result NEV_AccumulateCarriers` and `open AspisR1 AspisR1Stage2 Port3_NativeQueryBody`:

```lean
theorem result_state_effects {S Event : Type} (state : S) (base : Ops)
    (p : NEV_AccumulateRaw.Prepared) (a : NEV_AccumulateRaw.Accumulator)
    (node : U32) (value : RawE) (b : NEV_AccumulateRaw.BatchedWeights)
    (domain : Domain p a value b) :
    (do let out ← NEV_AccumulateRaw.accumulate_batched_with_node p a node value b
        ok (NFS_NEV_TailModel.toPair out,state,([] : List Event))) =
      (do
        let out ← AspisR1Stage2.verifier.accumulateWithOps
            (NBO_AccumulateAssociation.reference (NFS_NEV_TailModel.fields base))
            (toPrepared p) (toAccumulator a) node (toE value) (toWeights b)
        ok (out,state,([] : List Event)))
```

The theorem statement refers to the complete emitted function, rather than listing individual callees. It does NOT erase the conversion from its left-hand execution: NFS_NEV_AccumulateRaw_Funs.lean, loop1.body, lines 133–137, binds basis_at, executes CodeField.from_m31, and then calls trace.value 13. The external binding in NFS_NEV_AccumulateRaw_FunsExternal.lean calls the emitted NEV_CodeFieldRaw constructor, then maps its nominal carrier; trace.value itself is `ok ()`. The value is deliberately absent from the observable effect list. Its evaluation, including partial Result behavior, is retained and then proved total before erasure. Thus “callee not named by the packet” is too strong for the current NFS model forest.

The relevant exact canonical-domain association, namespace NFS_NEV_AccumulateCallees, is:

```lean
theorem from_m31 (ops : AspisR1.Port3_NativeQueryBody.Ops) (m : U32)
    (canonical : m.val<2147483647) :
    (do let out ← NEV_AccumulateRaw.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31 m
        ok (NEV_AccumulateCarriers.toE out)) =
      (NBF_RowInstall.install ops).op10 m
```

That law requires m.val < 2147483647. The stronger totality law actually used to erase the diagnostic conversion in the row-step proof, namespace NFS_NEV_CtorResults, is:

```lean
theorem m31 (word : U32) :
    NEV_AccumulateRaw.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31 word=
      ok (mValue word)
```

Here `mValue word := fromCtorE (NEV_CodeFieldBridge.value word)`. The active row proof names NFS_NEV_CtorResults.m31 and NEV_AccumulateRaw.trace.value explicitly. Its full statement (namespace NFS_NEV_RowStep, with Iter/RawFlow/Flow/mapFlow as defined there) is:

```lean
theorem active (ops : Ops) (v : alloc.vec.Vec RawQ) (power : RawQ) (next : Usize)
    (basis : Array U32 256#usize) (iter : Iter) (b : NEV_AccumulateRaw.BatchedWeights)
    (width : v.val.length=64) (finish : iter.end=64#usize)
    (inside : iter.start.val<64) (global : next.val<22) :
    (do let out ← NEV_AccumulateRaw.accumulate_batched_with_node_loop1.body
          v power next 64#usize basis iter b
        ok (mapFlow out)) =
      verifier.accumulate_batched_with_node_loop1.body (NBF_RowInstall.install ops)
        (mapVec toQ v) (toQ power) next 64#usize basis iter (toWeights b)
```

This establishes a model-side discarded-argument route already present in NFS; it does not grant native callee closure to the new OPEN trait-implementation rows, nor decide the lead's revised inventory status policy. No new compiler/prover run was performed.

For TX1:168 / Transcript<H>::queries, the NFX row has no selected claims and no CLOSED model packet. It is therefore impossible to quote a CLOSED full-function packet for that row. The existing successful-query model observation, in namespace AspisR1PublicPreparation.QueriesCalls, is:

```lean
theorem queries_success {H : Type} (B : QueriesModel.Boundaries) (D : aspis_core.Digest32 H)
    (self after : transcript.Transcript H) (row : U8) (payload : Slice U8)
    (out : Array U32 22#usize)
    (h : QueriesModel.queries B D self row payload = ok (.Ok out,after)) :
    ∃ absorbed blocks advances selected,
      transcript.Transcript.absorb D self row payload = ok absorbed ∧
      B.decode blocks advances = ok (.Ok (out,selected)) ∧
      after = {absorbed with state := selected}
```

This is conditional on model success and is NOT a native/model whole-function bridge. Its statement hides the embedding inside QueriesModel.queries B; the definition does not erase it. The tracked bridge-opening QueriesModel source declares:

```lean
structure QueriesModel.Boundaries where
  decode : Array (Array U8 32#usize) 8#usize → Array (Array U8 32#usize) 8#usize →
    Result (core.result.Result (Array U32 22#usize × Array U8 32#usize) aspis_core.transcript.QuerySampleError)
  embed : aspis_core.field.M31 → Result aspis_core.field.WideExact
```

All 22 sites bind `let we ← B.embed u` (with numbered locals thereafter) before `trace.value 5 ... we`; queries_success's proof destructures each B.embed success separately. Therefore the model names the embedding as a parameter and preserves argument evaluation; it does not by itself identify B.embed with the frozen WideExact CodeField implementation. NFS_NEV_AccumulateCallees.from_m31 is a potential canonical-domain association, not a supplied same-input query caller bridge. The query row stays OPEN, and its concrete B.embed installation/domain/native correspondence needs its own certificate. The source variant inspected here is identified by its path and hash in NGB_Q_SOURCE_PINS.json; no new coherent object association is claimed.

All quoted statements are verbatim retained source, with proof bodies omitted. Existing imports/abbreviations remain part of their meaning. No new theorem, axiom, trust item, or security closure is asserted; #print axioms is N/A for this inspection job. Existing NFS receipts are reused only as historical evidence, not replayed.
