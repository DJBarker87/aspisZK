# NJQ diagnosis of NJI-F1

Inspection only; 0 extraction used. Retained LLBC SHA256 77a8e51bbf032f627484418378f221106d5dbf951a59b365f98da1c42a64f0bc, NJI_EMITTED. All eight roots have Structured bodies, Transparent opacity and is_local=false. All four omitted roots occur in ordered_decls. They are absent even from the per-function translation timing table, so no symbolic body translation was attempted for them.

The pinned source PrePasses.ml::simplify_trait_calls (lines 3130–3217) computes used_funs from references inside Structured bodies and local definitions, then filters FunGroup declarations. Interp.ml::compute_contexts (115–159) translates only the surviving declaration IDs. The four roots are external statement-crate functions never called by any retained body. They are therefore removed before symbolic translation. Policy150 and validator157/206/208 survive because retained bodies call them. This is the exact omission mechanism, independent of body constructs.

| Row | Relevant constructs, separate from omission |
|---|---|
|152|bytes[176..].iter().any at frozen pair_forest_accounts.rs:445; IterMut.enumerate loop at :465; digest map_err and full Result|
|153|bytes[50..64].iter().any at :280; IterMut.enumerate loop at :296; identity/policy calls and map_err|
|201|No Iterator.any or IterMut. Reserved slice comparison and try_into/unwrap; status try_from and validator full Results, verifier_registry.rs:347–376|
|203|No Iterator.any or IterMut. Reserved slice comparison and try_into/unwrap; validator full Result, verifier_registry.rs:279–305|

The Iterator.any warning is a separate missing builtin trait field, not a causal explanation for registry-root omission. NJI-F1's earlier attribution is corrected here. No tool patch or LLBC edit is authorized or proposed. The additive NJQ selector must target the actual frozen statement package (same resolved deployed statement features) so these roots are local; it also makes the requested library operations opaque. Frozen files and old selectors remain unchanged. Record extraction outcome before considering (ah).
