# R331 monomorphized Option and nested-return preflight

Read-only inspection of the exact R312 `PrePasses.candidate.ml` and R327 LLBC. The source copies and line excerpt are hash-preserved; R330's translation command, result and failure log and R312's build receipt are included. No Aeneas run, tool build, LLBC extraction, or Lean compilation occurred here.

The selected `lower_nested_loop_returns` pass gathers every type declaration whose `item_meta.lang_item` is `Option`. For a function with a return inside a loop, it requires exactly one such declaration; it then uses the function's first local type as the return type and constructs `Option<return_ty>`.

R327 has three distinct Option language-item declarations: `Option<&B>` (type 9), `Option<usize>` (type 12), and `Option<Iter<B>>` (type 13). The emitted instantiated `Iterator::try_fold` functions 36 and 38 each return `ControlFlow<(),()>` and each contain one `Return` beneath a loop plus the final return outside that loop. Both loops are sourced from lines 2493–2497; the nested return is at line 2497. These are structural observations explaining the recorded prepass guard failure; the report does not select or recommend a rule for choosing an Option declaration.

R330's current failure is recorded with exact input and translator-binary hashes and no generated output. The earlier R303 erased-region failure remains historical evidence and is not described as R330's current first failure.
