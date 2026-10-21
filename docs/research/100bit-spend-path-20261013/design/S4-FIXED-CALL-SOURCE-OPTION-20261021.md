# S4 fixed-call source option for lead review

Status: candidate-only feasibility; production source unchanged. This is a recommendation to prioritize the equivalence proof, not adoption or closure of S4.

The current arithmetic value/execution chain is proved under the retained P6 array interpretation, but actual Rust `array::from_fn` reaches the mutable MaybeUninit implementation and remains an extraction/source correspondence boundary. Repeating scheduling or callback theorems cannot discharge that boundary.

The v10 source candidate (`lean-candidates/s4-minimal-fixed-calls-v10-20261021/`) avoids from_fn and has now been successfully extracted with Charon/Aeneas. It uses four explicit by-reference helper calls; the helper keeps the seven-batch/26-term schedule, makes both eight-limb updates and final reduction array explicit, and makes the two tail pushes explicit. Its exact source delta is larger than substituting the two array constructors. The extracted helper and outer entry are nonempty; the outer has slots 0,1,2,3 in order followed by Array.make4. Generated executable-body text agrees with the retained v6 candidate after declaration naming, which is a source comparison, not a kernel equivalence theorem.

The optimized NUC build and six finite fixtures plus strict stack check passed. Highest measured CU is 1,212,366 against a 1,400,000 per-transaction budget, leaving 187,634. Average regression is about 13,078 CU for stage1 and 15,695 for settlement. This is a potentially acceptable compute tradeoff for removing the extraction blocker; it is not a compute optimization and it exceeds the earlier 1.2M aspiration. It preserves the existing proof format and two-stage structure in the candidate. No numerical soundness bound changes are proposed.

Measurement qualification: the baseline source inventory covers 58 named paths; 56 match research 78812cfb5, with prover.rs excluded by features and r1_checkpoint_tests.rs excluded by cfg(test). This is not a complete release reachability proof. Fixture agreement is not source/effect equivalence or an analytical worst-case CU theorem.

Before adoption the following must be completed:

1. Prove the unrolled eight-limb term updates and batch fold updates equal the current source loop results, using the existing exact per-coordinate arithmetic and totality lemmas.
2. Prove the literal reduction array equals the original N8 callback result, reusing retained exact P6 N8 trace results while tracking the remaining old-Std boundary.
3. Prove the original two-tail iteration and explicit pair of pushes have the same states, failures and final value for the required accepted-run transport. The first g[28] push and final addition must remain ordered.
4. Compose the candidate helper and four-call entry with the same-g/source-prefix field/value theorem and the actual caller. The original-source proof and candidate-source proof must have separate pins; no historical source proof may be attributed to v10.
5. Assess affected S4/S8/caller source-cone pins, artifact hash/call inventory and any runtime obligations, then freeze/rebuild the complete adopted deployment artifacts and run the gates affected by that source change. No unrelated frozen cones need replay merely for this local candidate proof.

Current proven reference: `S4ForwardLiteralValueRootV1.four_dots_forward_literal_value` constructs complete generated P6-model execution, canonical outputs and four fixed-index literal head-plus-tail value equations from explicit caller parser/canonicality premises. The principal open part is implementation correspondence, not the head arithmetic sum.

The lead can retain the current freeze while these equivalence checks run. There is no reason to reject this path solely because it adds about 16k CU if the release budget remains 1.4M; nor is there justification to adopt it solely because six fixtures agree.
