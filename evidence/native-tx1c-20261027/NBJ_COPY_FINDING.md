# K048/K050 prefix-copy candidate finding

**OPEN. Not a shipped node_count counterexample.** K048 asserts the ordinary
slice-copy prefix/zero-suffix law on arbitrary16-word input and1<=n<=16.
It fails a property assertion (47 checks,1 failure), not an unwind check,
timeout, memory kill or graph-validation check. K050 requests the missing
counterexample artifact, same source with concrete playback enabled; it
reproduces that assertion failure. This is a permitted diagnostic for an
ordinary failed property, not a rerun of a timed-out shape. Both graph/lock
checks pass. K049 is EXCLUDED: CLI refused concrete playback without its
separate unstable feature flag. It is conservatively charged as a Kani
invocation; no proof ran. No Kani invocation beyond K050 is authorized.

K050's printed values: input[7]=1,input[15]=512, all other input words0;
n=16,k=15. This input is NOT strictly increasing, so an actual native
node_count call rejects it at well_formed before reaching its source copy.
It is inside the deliberately broader standalone copy harness domain;
it does not falsify a reached native count statement or a Lean theorem.

NBJ_R001 compiles/runs the exact selected slice-copy fixture with optimized
rustc1.94.1 (commit e408947bfd200af42db322daf0fadfe7e26d3bd1,
LLVM21.1.8,x86_64-unknown-linux-gnu), -Copt-level=3 and overflow checks on.
It prints expected512/actual512 and passes all16 coordinates. This is ONE
native fixture, not exhaustive verification, not a formal compiler/model
bug proof, not a complete node_count execution and not a source-to-ELF gate.
The concrete playback text is retained in K050/stdout.log; source, exact
command/tool pin/resources/exit are in NBJ_copy_native.rs.txt and R001 receipts.

Next concrete deliverable: isolate the pinned Kani slice-copy discrepancy
on the caller-proved strict/canonical admission domain (n<=16; both n10/n12
callers covered). Compare its selected trace with a genuine native replay;
then bind that SAME initialized array into NBJ_CountRows/CountLevels. Do not
replace the failure with an assumed final array, a claimed passing copy,
new trust item or narrower-than-caller invariant. Do not rerun any earlier
timeout shape or raise caps. The source per-cell copy gate NBI_K010 and the
new total count recurrences remain reusable predecessors, not this missing
complete native initialization port.
