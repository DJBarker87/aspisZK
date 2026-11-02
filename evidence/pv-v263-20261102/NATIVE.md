# Frozen-body finite native validation

N90120 and N90121 each use ONE admitted scope (6G high,8G max,swap0,tasks64).
No Kani or extractor run. rustc +1.94.1, opt-level3, debug assertions off,
overflow checks off, panic=unwind. Native inputs, commands, output, binary
hashes, reservation logs, GNU time, and compiler identity are committed.

This is an isolated frozen-source-body harness, NOT execution of the full
shipped client or its actual SemanticOracle. The only project modules compiled
are the byte-identical frozen host_work.rs and native_workers.rs. Their sole
conditional body feature is public-work-trace, disabled both here and in the
selected r1p-check + aspis-r1-cost-probe/ct-host-prover client configuration.
ct-host-prover's module selection is reproduced by the explicit path inclusion;
no rewritten helper/reference is substituted. No Cargo dependency resolution or
external crate is involved in this harness; alloc/core/std are those of the
recorded native compiler. This establishes helper body cfg parity, not a new
full-client feature-graph or artifact equivalence gate. Compiler preservation
of the complete deployed program remains V370.

N90120 (0.31s,156876KiB,swap0) checked output order and inner error retention
for the sumcheck counts, first source-order panic selection, and a task-slot
failure on stage200,count28. Count28 is NOT an actual C1 commitment count;
that first diagnostic is retained without attributing it to C1 capture.

N90121 changes the harness to include exact C1/C2 counts27/2, retains the ten
sumcheck counts and zero, and checks resource failure at stage200,count27.
It occupies 61 task slots with local joined handles in THIS task's capped scope,
then invokes the exact frozen helper. Scope::spawn panics with OS code11 before
ANY callback is called (local AtomicUsize counter stays zero). Handles are
released and joined; no thread is left running. The counter and synchronization
objects are harness-local; no writable static or Kani is involved. The ordinary
success checks pass for all thirteen counts, preserving a patterned inner Err
at each seventh index. A two-panic check resumes source-order payload2 rather
than17, while both hooks' stderr remains recorded. These are finite validations.

The resource-failure check is a source/runtime counterexample to unconditional
success over arbitrary runtime worlds, including a reached stage/count. Because
it occurs before callbacks, its failure is independent of the actual callback
body. It does NOT establish that an actual captured honest execution fails, and
does NOT refute existential Nonempty P. It also does not establish a successful
runtime world or source-to-native adequacy of the Lean world substrate.

fmt-1: no always-Ok formatting model is used. Actual panic diagnostics are
retained verbatim in native-results.json stderr. Modeling hooks, formatting,
allocation and unwind cleanup remains an explicit part of native worker binding.

## N90122 — changed configuration: deployed panic=abort and nested TLS

The exact same frozen helper bodies were compiled with rustc1.94.1,
opt-level3, debug assertions/overflow checks off, panic=abort. The new harness
checks nested map calls at counts0,2,27,28,14336, ordered outputs and patterned
inner Rust Err. Nested ACTIVE avoids new worker teams. Under task-slot
exhaustion (61 retained local handles, this task's TasksMax64 scope), reached
stage200,count27 terminates with Linux SIGABRT (-6), OS code11 from
scoped.rs203:46, with NO callback stderr marker and no normal return.
The host supervisor treats this exact abort as the expected passing control.
It disables core dumps; OS process exit reclaims all child threads. No other
scope or process was killed. The harness has no writable static.

This closes a missing finite configuration check in N90121 (which used
panic=unwind to inspect the panic), not a full source/native association.
The artifact is an isolated-body harness with exact helper cfg parity,
not the complete deployed client/crate feature graph or an actual capture.
N90122-receipt.json records target, source revision/input hashes, compiler
flags, expected signal, binary SHA, wall/RSS/swap and no-axioms applicability.
