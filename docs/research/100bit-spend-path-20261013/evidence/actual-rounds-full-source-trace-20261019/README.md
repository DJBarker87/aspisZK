# Same actual arithmetic rounds and full source challenge trace

RawAnnotatedSourceTrace constructs a SemanticRun and SourceFull25.Trace from the same AnnotatedRun used by the polynomial sumcheck chain. Every source call retains that run's actual q, record and ordered row schedule. The framed bytes equal the actual parsed record slots.

RawSemanticTraceDeterminism proves uniqueness of output challenges and final transcript for any two successful semantic runs or source traces on the same starting transcript and row schedule. It uses deterministic validated-record lookup and the actual semantic call. Different witness selections cannot introduce a second challenge list.

RawActualViewSourceChallenges identifies those source challenges, via the retained sampler carrier conversion, with the WideExact challenge components of viewPairs. Strict parsing plus successful actual rounds therefore yields both the semantic-view sumcheck chain and the matching source call trace. Challenge-list equality is derived, not assumed.

RawBeginAnnotatedFullTrace joins the actual begin success to that very same annotated arithmetic run. It constructs all25 actual calls in order, with q-list equal to the returned begin challenges followed by the annotated round q-list. The same semantic view's encodeFull equals the actual completed records, and decodeFrom on the constructed source frames returns that view's entries. Bounds on all framed source messages come from strict parser success.

All four focused native Lean4.32 targets passed, with printed axioms restricted to propext/Classical.choice/Quot.sound and zero process/cgroup swap. Exact source revision/bytes, object, imports, command, time, process RSS and capped execution admission are retained. These are focused component checks against pinned cached imports, not a clean unified owner/source release build. No package replay or cold build was performed.

Preserved diagnostics show the corrected failures: the first view-list check selected an incomplete AspisFormal cache root; the next required Function.comp_def rather than comp_apply for an unsaturated map function. The first full-trace candidate needed the dependent induction hypothesis applied to its suffix and used a reserved Lean identifier. None is accepted proof evidence.

Remaining obligations include composing the initial row0 and positive-row literal simulations with the actual caller, later circle/fold/query rows, current public terminal/evaluator/claims/library refinement, commitment/opening binding, full acceptance-to-Checks, universal query accounting, efficient extraction and the final source/artifact/CU/privacy release. The complete100-bit private-spend goal remains open.
