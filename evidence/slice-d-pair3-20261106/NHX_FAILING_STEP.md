# NHX failing steps

K001: own harness compile failure: duplicate Vec import and missing cfg(kani) allocator_api feature required by exact KMX include. Corrected in K002; no native credit.
K002: unwinding assertion in kani::Arbitrary array construction (64 cells; unwind6). No semantic mismatch and no timeout. Bound corrected to258 in K003; same resource/time caps. Not accepted as a negative control.

K003 passed length/capacity/pointer shape on an arbitrary initialized allocation (not a repeated-value prefix); K004 matched inversion fails. No closure until initialized VALUE/frame, KMX corruption control and coherent audits.

K005: filled initialized VALUE, arbitrary initialized64-cell allocation and arbitrary append index/limb, native Vec::resize(p+1,value). Solver timed out at90s (wall96.683s, peak6397704KiB, swap0). Tool limit, not a counterexample. Source hash and complete receipts retained. No unchanged rerun, no larger timeout or cap. Filled remains OPEN; dependent pair cannot assume its success or equality. Next isolate a smaller fixed write window; independent factored/dispatch/shared members proceed.

L024/L029: own ProcessKind model attempted unconditional substitution by NHI_Scalar.cohort, whose scalar law requires canonical SAME factor/power arrays. The simplifier correctly left this obligation. Corrected source model retains actual scalar calls; caller domains are developed separately, never added as successful-child premises. No false theorem or closure was accepted.

K076: real mismatch in OWN expected-call table, assertion `good` for factored-tail E operands. On side1/call12 the quarter stub records E argument pair(ap1[1],ZERO), but the table retained b12=er11 from side0's low*all call. Explicit witness: side1, i12, er11 nonzero. Corrected b12=ZERO on side1; actual frozen body/cut unchanged, twenty call positions and both operands still checked, no predicate weakened. K076 retained excluded; changed-source qualification starts K077, same harness name. K074/K075 tag observations remain valid, never rerun.
