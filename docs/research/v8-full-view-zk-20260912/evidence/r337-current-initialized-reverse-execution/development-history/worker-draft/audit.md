# R337 initialized-prefix and reverse-loop draft audit

Uncompiled scratch draft. It contains only two composed theorems and their complete `#print axioms` commands.

The first theorem composes R332's `selected_prefix_initialization_bundle` (output existence, length, canonical prefix reads, actual `selectedPrefix0` success) with R311's `batch_loop2_reverseModel`, taking its mathematical input length to be `L - 1`. The second uses R336's `second_prefix_bundle` for the actual `selectedPrefix1` result, R311's `batch_loop3_eq_batch_loop2`, and the same reverse-loop theorem.

Both statements explicitly require `xs.val.length = L` / `ys.val.length = L`, `0 < L`, canonical source reads for every `j < L`, iterator start `1` and end `L`, output vector length `L`, and arbitrary field input `x`. The proof derives nonempty source lengths, all prefix/reverse-loop read bounds, the reverse-loop output bound `L - 1 < output.length`, and the endpoint conversion `L = (L - 1) + 1`. It adds no inverse, nonzero, enclosing-caller-success, or extra-capacity premise. The output vector setup is not proved; its length is supplied explicitly.

No compilation, staging, tracked edit, or promotion was performed. Intended imports are R332, R336, and R311 only. The lead should check the generated theorem statements and run the required focused compile.
