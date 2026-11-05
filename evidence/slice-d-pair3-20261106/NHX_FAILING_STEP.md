# NHX failing steps

K001: own harness compile failure: duplicate Vec import and missing cfg(kani) allocator_api feature required by exact KMX include. Corrected in K002; no native credit.
K002: unwinding assertion in kani::Arbitrary array construction (64 cells; unwind6). No semantic mismatch and no timeout. Bound corrected to258 in K003; same resource/time caps. Not accepted as a negative control.

K003 passed length/capacity/pointer shape on an arbitrary initialized allocation (not a repeated-value prefix); K004 matched inversion fails. No closure until initialized VALUE/frame, KMX corruption control and coherent audits.

K005: filled initialized VALUE, arbitrary initialized64-cell allocation and arbitrary append index/limb, native Vec::resize(p+1,value). Solver timed out at90s (wall96.683s, peak6397704KiB, swap0). Tool limit, not a counterexample. Source hash and complete receipts retained. No unchanged rerun, no larger timeout or cap. Filled remains OPEN; dependent pair cannot assume its success or equality. Next isolate a smaller fixed write window; independent factored/dispatch/shared members proceed.
