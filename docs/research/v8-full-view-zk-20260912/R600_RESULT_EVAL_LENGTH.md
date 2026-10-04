# R600 successful result-evaluation length

R600 proves a structural fact about the finite word-program model: for arbitrary modulus `p`, retry budget, requested count, initial cursor, and deterministic response function `answer`, if `R580.resultEval answer (R572.limbs budget count cursor)` returns `some xs`, then `xs.length = count`. The proof follows the actual recursive result evaluator, retaining the failed-scan branch and the advanced cursor in the program definitions. The elements are `Fin p`, so each is canonical by construction.

The source is [R600ResultEvalLength.lean](lean/AspisV8R19/R600ResultEvalLength.lean), SHA256 `041653bea24420db195dbd40abc28875d92a8b7930bdfcc8422f9b85cd3d026a`, source revision `0c67bcfa00d1beea1f27742fdb6ab6a8e7eb62e8`. The theorem is named `resultEval_limbs_length`, with successful list and ending cursor implicit. It imports the pinned `R580SourceWordStream.lean` (SHA256 `297538faee8ac73ad4fe367e36ebf31e3938599dfa2eb371f2c82cb7d135e029`).

The focused cached-workspace Lean check used `-j1 -M4500`, `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, and `TasksMax=128`. Final attempt `1791091584775103000` exited 0 in 1.19 seconds; peak Lean-child RSS was 3,255,136 KiB and swap was 0. Complete axiom output:

```text
'AspisV8R19.R600ResultEvalLength.resultEval_limbs_length' depends on axioms: [propext]
```

All four focused attempts and their exact source, logs, and receipts are preserved in [evidence/r600-result-eval-length](evidence/r600-result-eval-length/). The first and third attempts failed due to proof-script issues. The second established the same fact with an earlier explicit-binder theorem name; the final check establishes the lead-requested implicit-binder `resultEval_limbs_length` statement.

This lemma supplies successful list length for R572/R580’s finite word model. It does not connect arbitrary finite block assignments to a coherent source hash oracle, prove an actual shared-oracle challenge law, or establish any sampler probability/security conclusion.
