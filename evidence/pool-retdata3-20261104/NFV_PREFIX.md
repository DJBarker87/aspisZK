# Production prefix / admission

OPEN. No production prefix certificate is established yet.
The frozen call graph has two different processes:

* Pool `pair_forest::process_pair_forest_terminal_with_verifier_v1` admits
  accounts/layout/marker and calls its `verify` closure; dispatch plans the
  selected verifier and encoded 320-byte request, then invokes it.
* Verifier `process_r1_cost_probe_instruction` calls `pool_route::admitted`
  after that CPI crosses the program boundary, before inspecting accounts.

`pool_route::admitted` is not a predecessor of Pool account admission in the
Rust call graph. A certificate must associate both sides of the actual CPI;
a reversed source order or an independently selected request does not suffice.
NFR_E002's missing process body is retained as a tool boundary. No extraction
rerun has been launched. The remaining work uses emitted child definitions
and a native full-prefix call log, not a new model named SameExecution.

NFV_K066 was a lane-input compile failure (fixed-array Box must first coerce
to a slice Box for into_vec). K067 corrects that and generalizes independent
proof/registry owners. K067 PASSES the actual frozen with-bytes planner's
accepted-return selected-program / SAME request allocation / arbitrary-byte
forwarding property. It uses an unconstrained typed registry result oracle;
no digest body is reached. Matched controls are still required.

IMPORTANT DOMAIN FINDING: these initial probes use empty account-data slices.
That is not a production registry PacketDomain. It is explicitly restricted
metadata-forwarding evidence and earns no production-prefix closure. Calling
this a complete admitted-account certificate would hide a stronger precondition.
The full prefix still needs all original account data/borrow pre-states at each
oracle call, request decode/encode association and layout-derived account windows.

Small-function extraction E001: Charon succeeded; Aeneas exited2 after66.683s,
533408KiB,swap0. Failure is `Unreachable`, InterpAbs.ml1955, merging abstraction
contexts at the request payment match (reference src/lib.rs12:18..18:9).
This is NOT a re-extraction of the forbidden process/HRTB spine and gives no
native/model closure. The sole extraction allocation is consumed; no rerun.
NFV_EXTRACTION_ARTIFACTS.json.xz preserves the427349-byte LLBC and pins once.
The source Cargo.lock stayed frozen; the separate reference lock added only
its intentional reference package. Every Kani graph/lock remains exactly frozen.

Generic NFV_Copy range/prefix/suffix/update and continuation laws now compile;
NFV_ListFrames supplies symbolic prefix/tail frame algebra. They are used to
connect the EXISTING emitted request envelope without concrete-buffer reduction.
These are model prerequisites, not a substitute for production caller domains.
