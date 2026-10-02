# R290 root-Fun0 ordering diagnostic

R290 applies a narrowly scoped metadata ordering preparation to the exact
R283 LLBC. It retains the R288 corrected root/dependency scanner, including
reachability-only default processing and the pinned singleton `TraitDecl`
nonrecursive rule. It extends only the singleton `TraitImpl 11` self-edge case:
that edge remains in the graph/census, is ignored for DFS ordering, and is
encoded as `{"TraitImpl":{"Rec":[11]}}`, matching both pinned
`reorder_decls.rs` lines 466–469 and existing `ordered_decls` serialization in
the R283 input. This is a metadata encoding rule, not a replacement body or
source semantics claim.

The ordering still fails closed at a different self-edge, `TraitImpl 2`, whose
name is under `core::slice::iter` and source span is file id 21, line 153. The
partial diagnostic records two witnesses:
`methods[8].skip_binder.generics.trait_refs[0].kind` and
`methods[54].skip_binder.generics.trait_refs[0].kind`. R283's original ordering
also serializes singleton recursive groups for both ids 11 and 2, but the lead
authorized only the id-11 extension for this task. Therefore no ordered R290
LLBC was emitted. The R288 diagnostic is preserved in
`R288-failure-diagnostic.json`; no translation or build was run.

Follow-up context: the exact original R283 input already carries 109 Charon
`ordered_decls` groups, including singleton recursive TraitImpl encodings for
both ids 11 and 2. This failed subset-reordering diagnostic is separate and
unnecessary for the original ordered input; its history is preserved.
