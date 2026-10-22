# S4 tx2 twelve returned local batches

This packet composes the accepted full tx2 source-cut success with the same-run typed-opening witnesses, resumed powers semantics, and four-slot current-array semantics. For each of the twelve reached `candidateCall` invocations, it retains that call's success and proves that the exact returned FullWide array decodes entrywise to four width-29 local batches using the C1/C2 decoded from the same 608-byte opening and the gamma from the same successful resume.

The theorem is `AspisR1S4Tx2TwelveReturnedLocalBatchesV1.full_tx2_twelve_actual_returned_local_batches`. It preserves the prior strict-scan premise, exact source powers output, same-array caller map, gamma canonicality, and pointwise source-power equation. All axioms are standard Lean axioms.

This is a formal source-cut result; it does not claim production adoption or discharge non-S4 source/Std boundaries. No Lean object is included. The launch Git revision was not captured and is recorded as unknown rather than replaced with the later repository HEAD.
