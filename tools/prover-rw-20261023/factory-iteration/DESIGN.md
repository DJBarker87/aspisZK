# ProverRwFactoryIteration design and acceptance criteria

Status: UNMERGED / UNADOPTED. Base 745f551f8485241f7b5e74bf5945169dbf14b1fb.
Only new job-owned tools/evidence/modules. No crates/programs edits, adoption,
trust change, protocol change, keys, network services, merge or push.

## Selected method

First try the installed Kani0.67.0 verified loop contract on a byte-exact
snapshot of selected64 generate_for_mask_nonce. The only source annotation is
cfg_attr(kani, kani::loop_invariant(...)) on its actual retry while. Erasing
that exact annotation must recover the immutable selected.rs byte for byte;
selected.rs must in turn match original source spans. No helper refactoring,
branch rewrite, loop truncation, source summary or destructor replacement.
Read-only installed help and macro inspection confirms -Z loop-contracts and
while-loop support. Hash inspected implementation and exact binaries before/go.

One iteration starts at retry r, 0<=r<16, calls=r, prior draws rejected,
last error absent. Fresh zero64 is filled once by the sole OS-boundary stub.
The postbuffer ranges over every initialized64 array, also on Err. The provider
u64 ghost token may change on every call including Err. It is bookkeeping,
not an OS-state refinement or probability law. For this primary run errors
range only over safely constructed custom-u16 codes; do not universalize them.

On Err the identical error returns via unchanged From and actual Drop runs.
On Ok both32 halves are copied into real Zeroizing owners. Success iff both
halves are nonzero returns those exact arrays and unchanged nonce, moving both
owners. Otherwise retry increases by1; the loop contract must verify base and
step, retaining calls=retry<=16 and prior rejection. This proves a finite16
control bound only if invariant establishment/preservation and caller assertions
all pass. At exhaustion retry=calls=16; the last allowed draw also rejected.
All actual destructors remain enabled. No destructor event count/order or
physical memory cleanup producer follows merely from executing them.

## Acceptance and failure rules

Reserve Kani055 for this actual annotated caller relation, all pointer/safety/
unwinding checks enabled, 240s timeout unchanged, same6G/8G/noSwap/Tasks64.
Before/go full hierarchy admission must be strictly below55GiB. No unchanged
resource retry. At most4 Kani,2 optimized Rust check/test,3 extraction,24 Lean
in this step; inherited54/60 Kani,49/52 extraction,236/260 Lean,15/16 backend.
No full BMC retry or frozen manifest. Do not use backend slot without a concrete
supported interface. Loop-contract failure must be retained with exact scope;
then isolate a source-exact single-iteration cut, label its caller association
and finite composition obligations explicitly open if unproved. Do not claim
a cut proves the whole execution. Source-exact cut means executable text is
selected from the actual body with a checked span map and only explicit entry/
exit plumbing, preserving real owner lifetimes and Drop.

Success requires complete receipts: exact command/target, exit, wall, GNU RSS
with killed-descendant limitations, sampled aggregate/cgroup peak, swap, revision,
source/dependency/tool hashes and full axioms (N/A for Kani). Retain all failed
approaches. Existing051/054 and Charon049 are reused component evidence only;
no new ELF identity gate. No theorem premises change; no output-equivalence
premise, forcedsuccess, nonzero assumption, freshness/E1/independence law.

Separate required producer: concrete actual caller/glue evaluation or reviewed
instrumentation-erasure/admissibility for real Drop events, including caller
provenance/order/lifetime. Leaf zeroize32/64 evidence alone does not supply it.
Outer8/adaptive proof_account, durable ledger, complete observations, E1/L1/L2/L3,
nativeclient/refinement/artifact and adoption/performance gates remain open.

## Fallback cut interface (designed before implementation)

If055 fails, preserve it without raising time/unwind/memory. Build a separate
ProverRwFactoryIterationCut snapshot with one_draw(mask_nonce, retry) returning
Result<(retry, Option<Self>), StateOnlyAttemptEntropyError>. Entry retry is
arbitrary below16; nonce arbitrary (including zero: caller admissibility is a
separate guard). It allocates the same64/32/32 owners and runs the verbatim
loop body, with only the success Result wrapped in (retry, Some(...)). The
rejection tail increments local retry exactly as the source and returns
(retry, None) AFTER the same lexical owner scope ends. Errors use unchanged ?
and From. Never make cut rejection look like actual factory exhaustion.

A generator checks every copied fragment and reports all signature/control/
return plumbing changes. This is a concrete candidate helper/cut, NOT verified
whole-caller equivalence: byte correspondence is useful source evidence, but
mechanized actual-body/caller/MIR equivalence and finite16 composition remain
open. The harness checks every entry retry0..15, freshzero64, arbitrary draw
outcome/postbuffer/custom-u16 error, exact returned arrays/nonce, rejection iff
either half zero, retry unchanged on success and r+1 on reject, and arbitrary
provider ghost advancement. Real Drop executes, event/provenance/unwind
transport stays open. Reserve056 for this cut relation only. No new Rust
check/test/extraction is justified unless needed for this concrete interface.

##057: explicit write set after055 timeout

055 timed out124/240s;056 single-draw candidate passes (462 checks,4 unreachable).
Read-only inspect001 shows dynamic-contract write-set inclusion loop in055's
instrumented artifact, alongside original-named loops. This is evidence of
instrumentation cost, not proof of its exact time attribution. Installed pinned
loop_modifies macro accepts a tuple of explicit pointer expressions. Reserve057
for a separate immutable annotated snapshot with explicit writes to retry and
six ghost statics (CALLS/LAST/LAST_ERROR/PRIOR_REJECTED/PROVIDER_STATE/LAST_STATE).
Fresh per-iteration local allocations must remain checked under Kani's frame
semantics. The source body is unchanged; no write set is assumed correct: all
checks stay enabled and any missing target must fail. Replace only the harness's
32-iteration returned-byte assertion loop with one arbitrary u8-mod32 index,
which quantifies all32 coordinates. Retain055 original files/receipt; do not
raise timeout/unwind/cap. This tests a concrete instrumented-write-set change,
not an unchanged resource retry. If it fails, retain it and stop this method.
