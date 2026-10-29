# Afterstate-box monitor finding: OPEN

K010 completed with one failed combined value/error/call postcondition. Its call-only split K011 passed and K012 failed the intended inverted condition. Pure selected-value native contracts K008/K013/K015 and controls K009/K014/K016 cover all three afterstate fields under an arbitrary typed successful child reply; K004/K005 cover all typed child errors at length688.

These fragments do not yet supply a defensible joint bridge: the mutable reply-observation association in the combined monitor remains unexplained. Removing allocation from the reference postcondition did NOT repair it: K017 (broader envelope length<=688) again completed with one failed postcondition. No claim that allocation caused the failure is made.

K018 attempted to recover the missing counterexample from K017's exact SHA-pinned GOTO artifact, using the same CBMC/caps and a selected-property trace at 90s. It timed out (exit124, wall94.391593497s, peak6411548KiB, swaps0). The partial trace is not a counterexample. No unchanged retry, larger timeout or cap increase. K010/K017 failures, K018 command/property/tool/source/GOTO pins and all partial outputs are retained. This is not evidence of a deployed Rust defect; no concrete failing Rust execution has been established.

Remaining exact obligation: diagnose the failed mutable-observation/result association (or provide a separately justified same-execution result interpretation), then compose the controlled call and value/error windows with NEC_AfterstateBox.emitted and NEC_AfterstateWindows.assemble against the CLOSED afterstate decoder on its actual caller domain. Until then decode_pair_afterstate_boxed_v1 stays OPEN and dependents do not cite it as CLOSED.

The live-snapshot decoder is independent of this member and proceeds bottom-up from its CLOSED digest/validator children. No field multiplication, SHA unwinding, Option<fn> or function-pointer-dependent observer is used. Rust map_err receives a zero-sized constructor FnDef; that is not an Option<fn> or a coerced function-pointer value.
