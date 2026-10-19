# User decision on G_R1.1 (2026-10-19): arithmetic savings

The two-transaction target of ≤1.3M CU each stands. It will be met by
arithmetic optimisation of the verifier, not by moving work between the two
transactions (J1.R13 showed a query move would put settlement at
1.413–1.429M, over the hard cap).

Target: about 120k CU of combined savings on the worst measured case
(withdrawal 255-pair: stage 1 1,339,527 and settlement 1,380,079), with both
transactions under 1.3M. The costed candidates are in the J1.R13 report
(`evidence/j1r13-artifact-20261019/checkpoint-report.json`); every saving is
labelled measured or unmeasured there.

Rules for this work, unchanged: every source change goes through the
standing gates (codec 1,233, ordered 583-call trace, checkpoint23,
injections, one SBF build with the stack audit, CU replay), no change to the
transcript or the challenge schedule without a new lead decision, and the
Lean extraction re-pins any changed declaration.
