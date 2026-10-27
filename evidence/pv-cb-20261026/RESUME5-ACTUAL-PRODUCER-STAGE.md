# Actual legacy tuple producer stage

Env-J 41249–41256 all passed. The accepted body proof uses the emitted loop
body unchanged, then proves loop equality, a successful-result offset invariant,
and root invariant for the extracted private legacy tuple_cells function.
The invariant holds uniformly over the explicit Range.contains parameter,
including selectors that fail or diverge; no template axiom is installed.
The carrier conversion and canonical caller transport discharge the offset
premise when that actual producer returns. The separate totality result covers
loop counts at most16. An explicit selector satisfiability witness is never
installed as the shipped implementation.

This is source-bound progress on a local producer invariant, not a discharged
source row or an endpoint-premise removal. The forest path uses its own helper;
nonpath forest translation changes rows via mutable iteration. Neither that
forest helper nor auxiliary translation is yet covered by these legacy proofs.
Trace-word canonicality and shipped-compressor/reference agreement remain open
inputs to the caller theorem. V164 P_source_p6 is unchanged.

Attempts41245–41248 were rejected during body-proof elaboration. Attempt41248
tried a local reducibility annotation; Lean rejected it. No unsafe-reducibility
option was enabled, and that annotation was removed before accepted41249.
All failed snapshots and diagnostics remain inert evidence.

Kani gates1–5 each timed out, with no verdict or source counterexample. Gate5
was compress16_lane2 with unwind18, canonical16 data/tag/lambda, timeout180,
wall3:00.00; its observed cgroup peak was3177398272 bytes and swap0. GNU time
wrapper RSS is recorded separately and is not represented as aggregate RSS.
The scope was confirmed absent or empty before the focused compiles above.

Forest extraction admission was refused without a scope. Its retained receipt
is charon-source-op223Forest-resume5-forest-001; the next attempt requires a
fresh name after at least180seconds. No failed gate was rerun unchanged.
