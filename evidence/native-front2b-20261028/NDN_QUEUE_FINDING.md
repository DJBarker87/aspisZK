# Native queue compiler-stop failure

K047–K080 invoked Kani but failed compilation with E0658 at the cfg attribute on the pattern assignment. They receive NO verification/control/closure credit. The client runner successfully collected each failing receipt and exited 0; the queue only stopped on timeouts, so it incorrectly continued through 34 compiler failures. This is a lane-owned driver mistake, not a frozen Rust or host infrastructure defect.

The repaired generator wraps assignment and try-expression statements in cfg blocks. The repaired queues require an exact PASS or intended single-check FAILURE and stop on every unexpected compiler/unwind/unresolved result. These repairs are unverified after the 80-run Kani limit. No extra Kani/codegen invocation was launched. No timeout or memory-killed shape was rerun unchanged, no cap increased, and no failure was renamed into a pass.

The final K080 was the originally scheduled result_field_window, not the late stronger active-frame candidate. The never-used scheduler override was removed. active_two_cell_window and active_outer_first_window remain UNRUN candidates. The proposed header counterexample K069 and additional u8 header-copy controls K076/K077 failed compilation too; neither is a semantic counterexample/control. Only the original pointer-copy controls K003/K004 are credited.
