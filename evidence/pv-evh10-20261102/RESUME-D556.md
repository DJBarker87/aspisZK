# D556 native entropy admission checkpoint

Resume base `8fdedd89e763194e907dd349404994937a95de5d`, branch
`codex/pv-evh-20261029`, same worktree and retained runjoin32 cohort.
**Target not yet established. Rows removed NONE.** This is a context
checkpoint, not budget exhaustion, an external blocker, or a counterexample.

## Before and after

Before: the deployed zeroize1.9.0 leaf was connected to opsNative, but the
Zeroizing constructor/borrow family remained residual and cleanup was joined
only to afterDraw's error fragment under an assumed original-slot lookup.
After: seven complete deployed wrapper bodies have structural source binding;
six wrapper operations plus the original zeroize byte/array selection pass
through opsNative. The original extracted entropy iteration's constructor,
array borrow, and ordinary error result are now connected to stack lifetime
admission, partial-fill physical writes, deployed1.9.0 cleanup, retired memory,
write/barrier history, runtime/allocator/errno frame and emitted events.
Original owners and coherent separate heap bytes are preserved under explicit
frame-admission and driver-heap-preservation hypotheses.

This is NOT complete native entry adequacy. The whole actual residual family,
real frame addresses/keys and native getrandom driver still need provenance.
Admission and a typed Delivery do not establish their native instances. No
uniform entropy answer/success domain or nonempty successful run is inferred.

## Accepted modules and exact scope

-79514 `ZeroWrappers`: transparent Zeroizing constructor, immutable/mutable
 dereference, AsRef/AsMut delegation, inner zeroize selection. Mutable backward
 functions are retained exactly. The source value law is not cleanup silence.
-79517 `StackAdmission`: physical writes explicitly convert UInt8 to Nat;
 inside/outside laws, original owner lookup, old live-region preservation,
 explicit heap coherence and heap/stack separation. A ghost initializer extends
 live slots; it does not invent a Rust allocation or invalid-memory branch.
-79519 `NativeZeroWrappers`: all six polymorphic fields installed at opsNative;
 constructor/borrow laws and inherited deployed1.9.0 array law. This chosen
 source installation does not yet pin the complete actual residual family.
-79521 `NativeEntropyBorrow`: actual emitted array AsMut dictionary and
 arbitrary equal-extent post-buffer restoration via Array.from_slice.
-79522 `StackEntropyFill`: typed full post-buffer, outcome, complete runtime
 state and events retained even on failure/fault/exhaustion; original lookup
 survives fill. Driver native association remains P. Runtime mutations are
 explicit, never silently replaced by the input state.
-79523 `NativeEntropyIteration`: actual extracted iteration source_error at
 opsNative and native run_step with original stack admission before fill.
 Success is an explicit UNIMPLEMENTED continuation; no full-loop credit.
 Source_error fixes only the reached getrandom call, not every world/answer.
-79526 `NativeEntropyIterationError.error_native`: joins the FULL actual source
 iteration Err result, zeroized physical region, complete post-driver runtime,
 retired slot, physical history and events. Extends79513 past its afterDraw
 boundary, but not past the driver's/frame's actual native association.
-79527 `StackEntropyCoherence`: admission includes initialized64, fresh key,
 heap separation and old live-region separation. Cleanup preserves coherent
 heap under driver heap preservation and retires exactly the newly admitted
 lifetime, leaving every preexisting live owner.
-79528 `NativeEntropyAdmission.error_coherent`: installs those heap/owner
 invariants through NativeEntropyIteration.run at opsNative on ordinary error.
 It requires Admission, input HeapCoherent, reached error and driver heap
 preservation. Those are P obligations, not trust fields or proved native facts.

All accepted theorems print only standard axioms. Exact targets, source git
revisions/blobs/SHA, dependency/object hashes, exits, wall/RSS/swap and axioms
are in receipt-ID.json/out-ID.log/time-ID.log. Accepted sources are immutable.

## Structural evidence and next callback work

`zero-wrapper-source.json` snapshots the already-pinned deployed1.9.0 source;
`zero-wrapper-binding.json` checks seven COMPLETE constructor/borrow/zeroize/
drop bodies. `zero_wrappers.py --check` is reproducible and runs in audit.py.
The new selection extends DeployedZeroSelected.selected: V221/V222 source and
physical laws are reused; the old extraction's1.8.1 effect law is not used.
V370 and L3 (registers/spills/copies/retired memory/joint observation) remain.

`entropy-iteration-binding.json` associates frozen project source, authoritative
unchanged extraction and native iteration error theorems. It explicitly marks
success, retry, inner32 and later disposal OPEN. Its checker is in audit.py.
No frozen Rust, extraction, release artifact or soundness source changed.

`callback-drop-source-inspection.json` inspects ALL seven RuntimeCallbackCtor
frames0,1,2,4,5,6,7: each lambda discards its argument and constructs a fixed enum;
all seven actual extracted captures are Unit. Six arguments are Copy enums.
TryReserveError is NOT Copy, but deployed1.94.1's complete struct/enum has only
TryReserveErrorKind, scalar Copy Layout and unit fields, with no custom Drop.
The source-only checker pins the project files, extraction Types, and full
collections/layout source snapshots in callback-stdlib-source.json.
**This is inspection, not a new native callback theorem or installation.**
Next: bind those exact argument/capture/unused drops and install all seven
through RuntimeOperators at NativeOperators.selection. Do not use a generic
always-ok handler, infer silence from Result purity, or erase unwinding or L3.
Writer/syscall/returned io::Error destruction is a DIFFERENT, still open cone.

## Failures, staging recovery and resources

This resume used15 charged attempts79514–79528:9 accepted/6 failed.
79515 mixed UInt8 with Nat physical bytes; changed conversion passed79517.
79516 lost explicit ExternalTypes/poly field binders;79518 corrected carriers
but still implicitly instantiated polymorphic field equality.79519 uses full
@ExternalFuns.op fields and passed.79520 lacked the equal array extent in
from_slice restoration;79521 proved it.79524 introduced theorem let-bound
world/delivery as hypotheses;79525 fixed that but had a syntactically hidden
outcome match and a no-progress dsimp.79526 names the delivery status and passed.
Failed sources remain recoverable at receipt revisions; no unchanged retry.
Max new peak RSS4,470,068KiB, slowest7.00s; cumulative max4,616,200KiB. Swap0.
No kill, timeout, cap increase, admission refusal or transport fault.

The first stage stopped locally before a host action: the inherited optional
restage of accepted79513 had overwritten its preparation with a self-predecessor
entry. Its receipt-bound original was already archived. Restored that exact
snapshot, archived displaced bytes, and recorded resume-stage-recovery.json.
No script/guard/LEAN_PATH/J.json/shared object/library authority changed;79514
was still unlaunched. Sparse git add needed --sparse; no build was launched by
that failed git command. A callback checker prefix-match bug was corrected
before the final read-only audit; no compiler attempt was involved.

## Remaining ordered obligations

1. Establish actual full residual dictionary family and real source/native
 frame/address/key provenance; Admission is still a conditional invariant.
 Bind the actual getrandom driver (every return/fault/prefix/errno and mutable
 write), then success/inner32/retry/later-secret drops through the full entropy
 and proof-account entry. Do not treat arbitrary Delivery.runtime as native.
2. Native heap metadata/padding, Rust1.94.1 RawVec/Global/System ValidAnswer,
 owner-indexed Vec propagation through ACTUAL consumers and allocator-world
 association remain open. RuntimePublishInstall still uses old CapacityWorld.
3. Install seven now-inspected callback frames; bind literal diagnostics,
 writer/syscalls/io::Error drops and installed hook/backtrace/profile under
 D474(C). No core::fmt Unit assumption or old dynamic std OOM formatter.
4. Cover remaining path/digest/options/hash/oracle-byte/primitive/restoration
 leaves and COMPLETE Q/stack proof-account entry. Old entry_fixed is source
 P/FinishedView transport, not native heap or observation adequacy.
5. ONLY THEN prove unchanged oraclePrefix/countTrace/nonce-store fileTrace on
 actual provenance-fixed families, retaining D520/U/D524 client inputs.
6. ONLY THEN (v-prime) reduces consistency to successful actual worldRun
 nonemptiness at opsNative AND the allocator world. NativeObstruction62/op132
 remain. No unrelated MODEL witness or new T item earns closure.

## Checkpoint

Read-only audit.py reconciled all47 receipts, accepted sources/objects, source
checkers and no-live-scope host state. Native closure preflight still fails as
required. validation.json/host-final.json are current. No final compiler audit,
closure or frozen manifest replay was run. Both audit triplets are untouched.
Cumulative47/100:31 accepted/16 failed. **53 remain; NEXT79529.**
T unchanged. ALL endpoint/deployment/privacy rows unchanged. V370/V371,
rdea-1/V400, D159/D166, L1/L2/L3 and named client fields remain obligations.
No delegation, push, other-worktree write, native/Kani execution or key/account/
funds action. commits-D556.txt records source stages before this evidence commit.
