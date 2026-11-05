# NHX failing steps

K001: own harness compile failure: duplicate Vec import and missing cfg(kani) allocator_api feature required by exact KMX include. Corrected in K002; no native credit.
K002: unwinding assertion in kani::Arbitrary array construction (64 cells; unwind6). No semantic mismatch and no timeout. Bound corrected to258 in K003; same resource/time caps. Not accepted as a negative control.

K003 passed length/capacity/pointer shape on an arbitrary initialized allocation (not a repeated-value prefix); K004 matched inversion fails. No closure until initialized VALUE/frame, KMX corruption control and coherent audits.

K005: filled initialized VALUE, arbitrary initialized64-cell allocation and arbitrary append index/limb, native Vec::resize(p+1,value). Solver timed out at90s (wall96.683s, peak6397704KiB, swap0). Tool limit, not a counterexample. Source hash and complete receipts retained. No unchanged rerun, no larger timeout or cap. Filled remains OPEN; dependent pair cannot assume its success or equality. Next isolate a smaller fixed write window; independent factored/dispatch/shared members proceed.

L024/L029: own ProcessKind model attempted unconditional substitution by NHI_Scalar.cohort, whose scalar law requires canonical SAME factor/power arrays. The simplifier correctly left this obligation. Corrected source model retains actual scalar calls; caller domains are developed separately, never added as successful-child premises. No false theorem or closure was accepted.

K076: real mismatch in OWN expected-call table, assertion `good` for factored-tail E operands. On side1/call12 the quarter stub records E argument pair(ap1[1],ZERO), but the table retained b12=er11 from side0's low*all call. Explicit witness: side1, i12, er11 nonzero. Corrected b12=ZERO on side1; actual frozen body/cut unchanged, twenty call positions and both operands still checked, no predicate weakened. K076 retained excluded; changed-source qualification starts K077, same harness name. K074/K075 tag observations remain valid, never rerun.

K101: process_kind combined parts/scratch frame on the whole source cut TIMEOUT90s (wall96.704s,peak3133432KiB,swap0). No credit, unchanged rerun or cap/time increase. Isolate the return/parts write and the Vec/slice selected-word window; reuse K089–K100 passing prefix/argument/Result/finish observations. The independent source-order family is still unattempted and may proceed. Parent row remains OPEN.

K113: regular full-carrier reply corruption control TIMEOUT90s, no credit for that pair; K112 is unpaired support only. Isolate typed E[7] selected-word copy and Unit/Error reply transport, composing the already passing whole source-order/first-error control and full argument/carrier observation pair. Reuse K106/K107 Q64 selected-word window plus compiled word lift, never rerun an unchanged timed-out shape.

L018 initial own target `final` was refused by the NHX-prefix guard before source upload/launch. Corrected to `NHX_final`; one admitted audit process only, no process resubmission or budget double counting.


K101: process combined scratch/parts observation timeout90s; replaced by K102–K107 independent control, suffix return/frame and one-word adapter cuts, each matched corruption qualifies. K113: full regular carrier corruption timeout90s; K112 positive is support only; K114–K117 independent E-word and Unit/Error carrier pairs qualify. K118: actual zero64 allocation initialized-prefix/frame timeout90s, remains OPEN; K119/K120 single-cell native support does not close it. No unchanged timeout rerun, cap or timeout increase. K076: erroneous harness expectation for side1 b12 operand, corrected to ZERO and requalified by K077/K078. No Rust mismatch established.


Lean proof repairs are preserved per attempt. L068/L069/L071–L074 FinalTotal active-step proofs failed on explicit Inv unfolding, iterator/match and let-binder elaboration; L075 fixes the explicit monadic continuation and compiles with standard axioms. L076/L077/L078 LowScale failed on namespace/opaque QUARTER unfolding; L079 uses the inherited symbolic LPf_BaseMultiply source law and small constant arithmetic and passes. L080 LowDomain lacked NHI_RangeProgress import; L081 adds it. NHX_ProducerLoops.unproved.lean.txt is a retained, never compiled proposal, excluded from the import/roots/credit. No failed elaboration or its generated error placeholder is a certificate.
