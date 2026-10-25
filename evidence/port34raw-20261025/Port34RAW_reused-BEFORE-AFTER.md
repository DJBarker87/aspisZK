# Query31 proposed conclusion change — UNCOMPILED

No premise changes are proposed. This is a reconstruction of the visible358
mismatch in the published source notation, NOT a complete actual raw-type
export. CLI359 failed before raw reads. Original actual selected type/value
remain only in pinned released DATA; neither candidate nor bridge was checked.
All H/B/D/self/after/row/payload/out/h binders and outcome carriers remain.
No extra execution/equality/head-state hypothesis. Only the indicated conclusion
is added; absorb/decode/after/length/stateChain/materializedOutputs all retained.

Before (Calls shape required by358 diagnostic, reconstructed):

```lean
theorem queries_success_with_digest_pairs_full {H : Type} (B : QueriesModel.Boundaries)
    (D : aspis_core.Digest32 H)
    (self after : transcript.Transcript H) (row : U8) (payload : Slice U8)
    (out : Array U32 22#usize)
    (h : QueriesModel.queries B D self row payload = ok (.Ok out,after)) :
    ∃ absorbed blocks advances selected,
      ∃ pairs : List (DigestPair D absorbed.hash),
        transcript.Transcript.absorb D self row payload = ok absorbed ∧
        B.decode blocks advances = ok (.Ok (out,selected)) ∧
        after = {absorbed with state := selected} ∧
        pairs.length = 8 ∧
        stateChain pairs ∧ materializedOutputs pairs blocks advances
```

After (published source candidate, not established in actual context):

```lean
theorem queries_success_with_digest_pairs_full {H : Type} (B : QueriesModel.Boundaries)
    (D : aspis_core.Digest32 H)
    (self after : transcript.Transcript H) (row : U8) (payload : Slice U8)
    (out : Array U32 22#usize)
    (h : QueriesModel.queries B D self row payload = ok (.Ok out,after)) :
    ∃ absorbed blocks advances selected,
      ∃ pairs : List (DigestPair D absorbed.hash),
        transcript.Transcript.absorb D self row payload = ok absorbed ∧
        B.decode blocks advances = ok (.Ok (out,selected)) ∧
        after = {absorbed with state := selected} ∧
        pairs.length = 8 ∧
        (∃ first rest, pairs = first :: rest ∧ first.state = absorbed.state) ∧
        stateChain pairs ∧ materializedOutputs pairs blocks advances
```

Proof must retain successful QueriesModel.queries execution decomposition. The
published body derives self1 from the actual absorb bind; pair0.state is
self1.state by its constructor, and pairs is the finite list pair0..pair7.
At the final conjunction introduction insert the witness
`⟨pair0, [pair1, pair2, pair3, pair4, pair5, pair6, pair7], rfl, rfl⟩`.
This is a finite symbolic construction within the execution proof, not a
consequence of arbitrary list length or stateChain. Complete reference body is
retained in reused-reference358-Query31SourceCalls.lean.txt. It must be ported
against actual exported weaker proof binders/dependencies, then normally checked
as an explicitly NEW origin, followed by the unchanged actual Bridge.

Rejected directions: infer head state from length/stateChain; add head-state as
premise; weaken Bridge; invoke proof irrelevance to convert unequal propositions;
claim published text equals actual selected ConstantInfo. None was attempted.
