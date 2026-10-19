# Semantic-round success preserves the actual check equations

Successful execution of RoundModel.step now yields the same validated record and decoded 28-coefficient polynomial, the actual boundary-call result, a false result from the source equality comparator, equality of that boundary with the incoming running claim, the actual sampled challenge and transcript, the exact alpha update, and the actual value-call result equal to the outgoing running claim. None of these successful arithmetic/decode outcomes is an added premise.

The earlier RoundCalls.step_success proof already reached these facts but retained only record/challenge/alpha information. This theorem reuses that proof structure and the structural QM31 comparison proof from ActualFinishTerminalComparison to retain the missing equations. It uses the exact already compiled Model/Reachability sources and objects rather than rebuilding the extraction chain.

The focused Lean 4.32 target passed in 11.51 seconds, peak RSS 2,253,881,344 bytes, zero process swaps, with only propext, Classical.choice and Quot.sound. Exact command, compiler, source revision, source/object/import pins and axiom report are retained. The first changed attempt omitted a local classical instance from the reused comparison helper; it failed and was replaced by the corrected source, without increasing memory limits.

Boundary implementations remain explicit parameters of RoundModel. Concrete decode/Horner/boundary implementation correspondence, ten-step aggregation, source accepted execution to the literal transcript/readers and sumcheckChecksZ, and the final protocol/ROM/security theorem remain open. This packet proves neither complete Rust refinement nor 100-bit soundness.
