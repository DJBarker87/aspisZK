# Checked statement and proof delta (call363)

The complete exact actual before/after Calls types and both complete Bridge types
are in Port35ANCHOR_types363.json. That file's construction-stage status precedes
the successful checks; Port35ANCHOR_result363.json and charged attempt363 are the
final result. No statement in this document replaces the raw types.

Readable original Calls statement (same source namespaces/notation as reference):

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

New public kernel theorem (same namespaces/notation for readability):

```lean
theorem Port35ANCHOR.queries_success_with_digest_pairs_full {H : Type}
    (B : QueriesModel.Boundaries) (D : aspis_core.Digest32 H)
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

Original Calls is normally checked unchanged under its exact original name.
The new theorem changes no input, successful-execution premise, type carrier,
projection, quantifier, output, decode or absorb equation. Its only additional
conclusion is the first-state anchor between length8 and stateChain. Strict
inverse removal of that one insertion reproduces the entire original Expr type.
No assumption was added, changed, discharged or hidden in a structure. The anchor
obligation is now derived from the same successful source execution.

The actual proof walk visited175420 distinct strict expression nodes, found one
terminal constructor site at binder depth725, pairs#24/absorbed#715, and resolved
the actual local `pairs` eight-cons list and `pair0` typed constructor. Explicit
finite witnesses pair0/[pair1..pair7] and definitional reflexivities establish the
anchor.343 distinct result-tail occurrences in the actual proof's type arguments,
Exists predicates and enclosing execution-elimination motives were strengthened.
This count is runtime AST evidence, not inferred from old text offsets. No source
text substitution, generic wrapper, new premise, or broad reduction was used.

Original Bridge is
`AspisR1PublicPreparation.Query31SourceSchedule.queries_success_pairs_functional_full`.
Its entire original TYPE/level parameters/name/all metadata are STRICT-IDENTICAL.
Its VALUE changes ONE constant reference from original Calls to the new theorem,
retaining levels and every other Expr node/metadata. Strict inverse substitution
restores its original value. This is an explicitly NEW proof variant/re-pin,
never an unchanged Bridge body or historical source-context identity claim.
Full unchanged Bridge statement is in the exact type JSON; no dependent premise
was weakened. Normal strongCalls check precedes revisedBridge in one context.

Boundaries.decode/embed, DigestCall source slice/tag/input/digest equations,
DigestPair shared-state/tag equations and indexed materialized readbacks retain.
All SDK/std/runtime/allocator/extraction/child/history/event/mark/P2Prime/native/
source/artifact boundaries retain. This focused accepted-execution result is not
adaptive oracle/event-law transport or a complete security theorem. Both security
targets remain NOT ESTABLISHED.
