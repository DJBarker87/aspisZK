# Generated powers array totality and complete caller equality

PROVED: generated_trace_lifts inserts the actual Usize cursor into a retained source powers trace. Every generated FnMut step executes its checked source callback and successful cursor addition; start+count<=Usize.max proves no cursor overflow. The last increment reaches N itself, so all Usize array lengths are covered without a small-N or work-normalization assumption. The generic callback-operation identity remains explicit for reuse.

PROVED: sourceArrayPowers_total discharges that operation identity by reflexivity for the exact sourcePowerCallback record and reuses retained canonical powers totality. The resulting P6 generated array-interface powers operation succeeds for every canonical input and Usize N. sourceArrayPowers_eq_claimPowers proves equality of complete Results and raw arrays with the retained checked claim implementation, without a successful-run premise.

PROVED: prepared_claim_sourceArray_eq lifts that equality into the whole retained claim caller. It covers its complete Result, including errors/divergence, and removes the earlier one-way successful-output limitation. Existing powers/claim algebraic proofs can now be reused under this generated-interface model on canonical kappa.

OPEN: the explicit P6 Rust standard-library correspondence and actual enclosing extracted source/caller installation; the rest of the preparation, sampler, arithmetic/source/runtime/artifact obligations and global 100-bit theorem. These claims do not constitute an unconditional Rust Std proof or completed implementation soundness. No production Rust, CU, ELF or deployment changes.

Focused NUC Lean4.32 -j1 -M4400 check: exit0,2.308s,scope379879424B,swap0,High1GiB/Max2GiB. All four exported axiom reports are standard only. Initial draft failed on small pair/let reductions and an unresolved scalar-bound representation; explicit rfl and the existing scalar bound tactic fixed them. Failed diagnostics retained; no resource increase or package replay. Exact source/import/compiler/command/admission/resource evidence retained; no binaries.
