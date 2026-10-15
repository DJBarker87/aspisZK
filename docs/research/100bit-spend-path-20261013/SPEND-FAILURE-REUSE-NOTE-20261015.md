# Reused extraction and q22 support facts

`AspisR1.SpendFailureSupport.matchingSet_card_le` composes the existing `AspisR1.SpendExtraction.large_matching_extracts` theorem with contradiction. Its only new conclusion is the contrapositive support-size fact: under the extraction theorem's original premises, if no listed candidate satisfies production, copy-link balance, and `SpendSemantics.NoteFacts`, then the matching set has at most 9557 elements.

`matchingSet_q22_successful_containment_bound` applies the old `R0C.V3.Q22.q22_bound` to that exact set. The old theorem bounds the law of a successful 22-element query set contained in any fixed support of size at most 9557. The new wrapper does not identify the unified transcript's query sampler with that old q22 law; it states the law at the old theorem's interface.

Sources: [SpendFailureSupport.lean](lean/SpendFailureSupport.lean), [SpendExtraction.lean](lean/SpendExtraction.lean), [Q22Law.lean](../v8-r0-close-20261007/lean/R0C/V3/Q22Law.lean). The focused evidence and axiom report are in [lean-spend-failure-support-20261015](evidence/lean-spend-failure-support-20261015/README.md). This note makes no D1/D2/D3 or knowledge-extraction claim.
