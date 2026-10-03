# R434: actual fold control and unsafe-precondition helper capture

R434 exposes the two previously opaque native unsafe-precondition helper bodies used by the selected fold. It preserves the actual fold, callback capture and cleanup paths. This is source extraction and structural evidence, not a Lean source-execution theorem, privacy proof or soundness proof.

## Capture and custody

Exact target: `R434ActualFoldUbHelpers.llbc`. Source revision at launch: `f997fffc34b60ebf9a93e80b8edbdc96485ae9d6`. SHA256: `7c03a7576da2d380749bdd48a9ded791e4563d6fb3b6834ef4d15665f479b96e`. Charon exited 0, `has_errors=false`, wall time 13.79 seconds, GNU peak RSS 630,388 KiB, swaps 0. Terminal cgroup peak was 494,043,136 bytes, zero swap and no OOM/high/max events. GNU and cgroup measures are retained separately; their difference is unexplained in the saved records. Axioms: not applicable to this diagnostic LLBC capture; no Lean job was run for R434.

The command differs from R431 only by two narrow includes, `core::ptr::const_ptr::_::offset_from_unsigned::precondition_check` and `core::num::_::unchecked_add::precondition_check`, and a fresh destination. The verifier and original Charon driver were unchanged. Source hashes, wrapper/driver hashes, nightly Rust commit, selected feature/flag set, cached offline/locked release command, resource caps and host reservation checks are saved. The job ran with MemoryHigh=5 GiB, MemoryMax=7 GiB, MemorySwapMax=0, TasksMax=128. Independent capture audit and lead inspection passed; no unchanged capture or regression was repeated.

## Source facts

Native helper114 compares its pointer inputs using `Ge`. Its successful arm continues to return; its failing arm retains message construction, panic call, unwind cleanup and UndefinedBehavior abort. This check alone does not establish same-allocation provenance, alignment, lifetime, or valid pointer distance.

Native helper115 casts both usize operands to u64, performs `AddChecked`, and reads the tuple overflow field. The false-overflow arm returns before the failure tail. The true-overflow path retains its complete message/panic/abort behavior. These bodies are now Transparent/Structured. They remain subject to a source primitive and representation bridge; recording their operations does not prove execution.

The full Fun70 inventory records 326 nested statements, both UbChecks sites, Global31/32 uses, intrinsic distance, pointer offset and dereference, mutable closure borrow and moved call arguments, unchecked addition, exit equality, break/continue, drop and unwind chains. A strict normalized comparison shows Fun70 equal between R431 and R434 after expanding capture-local hashcons/dedup and removing only spans and statement IDs. No operation, local, type, generic argument, branch, error or cleanup was dropped by the comparison.

The captured callback Type50 contains a mutable reference to power and a shared reference to gamma. Fun112 reads power, multiplies by the slice value, adds to the accumulator, multiplies power by gamma, and writes power back. The native fold uses FnMut with `Move(Local17)` after constructing a mutable borrow of closure Local3. The inventory identifies trait method0 and the matching call_mut metadata, while explicitly retaining the empty native implementation methods array; it does not silently assert dispatch resolution. Captured drop-glue bodies are retained, rather than assumed away. Caller slices are exactly 359..388 and 388..417; the first batch is evaluated again for the intercept.

## First remaining proposition

Prove correspondence for the recorded helper guard operations and native loop state, then bind the complete fold through pointer distance, casts, read validity, unchecked arithmetic, mutable borrow restoration, storage frame, callback dispatch and cleanup/error behavior. R435 addresses only the scalar guard and modeled pointer-order facts, with explicit boundaries. Source allocation/value images and primitive ABI/provenance/lifetime arguments remain open. Vec::extend and complete callback chronology remain open.

Universal joint C1/H1/G compatibility, the entire published-view simulator with faithful shared oracle and explicit losses, coherent quotient extraction and optimized-to-source acceptance are not proved. Genuine 999,790 / 999,532 CU and every security parameter are unchanged. No deployment, merge, transaction or wallet operation occurred.
