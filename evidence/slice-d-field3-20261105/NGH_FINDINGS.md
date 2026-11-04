# Findings in progress

F1: Kani 0.67 loop_invariant macro accepts while loops only (pinned installed source library/kani_macros/src/sysroot/loop_contracts/mod.rs lines 569/574); the actual frozen accumulation helper has nested for loops. A whole-array proof_for_contract would violate this job's rule-B one-iteration restriction. No source rewrite or whole-loop result is admitted. The precise remaining obligation is an actual-function contract supported by a native arbitrary-prestate step/Lean induction certificate; existing cuts alone do not instantiate proof_for_contract on the frozen body.

K001 is an own harness-input error: weak_shape lacked its required proof_for_contract harness, so Kani rejected the entire crate. K002 adds that missing harness without weakening validation. K001 has no proof credit.

L002 is a failed proof draft (bind association), not an accepted theorem. Its sorryAx diagnostics are excluded; the next draft associates the nested cache binds before induction.

K010 expectation-field correction: the inherited runner label erroneously said outer data step. The command actually checks the loop-free QM31 square contract with deterministic natural-coordinate constraints on nondeterministic CM replies. Expected heavy time is solver elimination of those constraints, not extraction or large proof generation. The label is corrected for subsequent attempts; the original receipt is retained unaltered.

## Correction: F1 withdrawn

Full macro inspection found a ForLoop conversion at lines 471 onward before the later while-only branch. The initial inspection of lines 569/574 was incomplete. Thus F1 is NOT an unsupported-loop blocker and the question to the lead was based on a false premise; no permission to change the requirement is needed. Continue the actual invariant route. K021 is an own-input missing proc_macro_hygiene feature error, not an unsupported-for verdict. L017 is an own review-directory collision: the generator reset the output directory; change the own script back to a fresh wide-stage directory and repeat the unlaunched review step with new inputs. No proof replay occurred in L017.
