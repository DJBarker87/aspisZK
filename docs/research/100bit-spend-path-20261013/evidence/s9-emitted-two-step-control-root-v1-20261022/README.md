# S9 emitted two-step control

`helper_success_two_body_calls` starts from successful execution of the actual emitted `factored_s2_libra_weights_loop` at its source range [0,2] and an arbitrary initial array. It derives the actual first `.cont` state/array, the actual second `.cont` state with the same final output, and the terminal `.done` call. The iterator values/bounds are derived from the retained checked RangeIter contracts. No successful body-call premise is assumed independently.

The imported leaf proves that a successful active body must return `.cont` at the same next iterator. Its `body_some_eq_activeBody` is a kernel-checked equality between the emitted body and the explicit active source suffix under the actual successful next result. The same arbitrary FieldOps instance is retained throughout. No field semantic law is assumed to prove this control fact.

This is an accepted-run decomposition, not proof that the helper succeeds or has the right arithmetic output. The P6 from_fn/library, concrete arithmetic meanings and caller/source links remain separate. No full S9 or global soundness closure is claimed.

Both focused Lean4.32 targets are green. Leaf:15.486s, process peak2,240,954,368 bytes; consumer:25.672s, process peak2,226,651,136 bytes. Both observed swaps0, clean monitored mutex/foreign-process observations, standard axioms only. The consumer audits all three named claims. Exact source/import/object pins, argv/profile, metrics, raw logs and controller source included; compiled objects excluded. Earlier failed drafts remain in the working candidate history and scratch attempt directories, not accepted proof evidence. No unchanged full regression or verifier-source change occurred.
