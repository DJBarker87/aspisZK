# D575 continuation — target not yet established

Entry e51b510e58, same sparse worktree and codex/pv-runjoin-20261026 branch.
Latest proof-source revision 304f4c6ff2; later commits pin validation/evidence.
No push/merge or frozen Rust edit. All three requested endpoint obligations
remain OPEN: complete native worker binding, actual opsNative installation,
and successful actual reached capture. Nonempty P remains unproved.

## Established source-store work

RetainedMethods preserves both Vec reservation lower bounds across append;
the donor is emptied without losing its reservation. append_erasure proves
complete-run equality to VecSpine.append on the proved length domain. A granted
reserve extends a LOWER bound with max(old bound,new length), not a claim
about exact physical allocation capacity.

RetainedSpine substitutes BufferFamily into the inner site and carries Buffer
through EVERY outer item/family/handle/caught/output store, including the actual
delayed Task bodies. TrustedLen stores use an initial room invariant. Both
append owners are returned; the donor reservation survives to its drop hook.
This port is accepted but is NOT a native runtime or an actual installation.
Its method/drop hooks still need faithful interpretation; in particular native
reserved push/append do not acquire arbitrary allocation-failure branches.

RetainedFacts proves length, completed and reservation invariants for arbitrary
callback/resource outcomes. It assumes no successful callback vector.
RetainedErase proves COMPLETE Q equality after erasing reservation metadata for
push and collect stores: faults/exhaustion/source fail/div, post-world and event
prefixes are preserved. Whole-spine erasure and native heap association are not
claimed by these local theorems.

TrustedStores models the pinned SetLenOnDrop distinction: local initialized
length advances at each raw store, while the borrowed published Vec length
stays unchanged until guard drop. write_order bounds the increment; publication
changes only the published length. erasure gives complete Q equality to the
retained collector. No unwind destructor is fabricated under panic=abort.

OwnedDrain separates a reservation lower bound from capacity derived from an
owned allocation descriptor (pointer token, raw capacity, layout; ZST special
case). drain preserves both descriptors and empties the donor. It proves no
physical reserve growth under the room bound, even when the actual capacity
exceeds the lower bound. The empty donor's release descriptor uses ORIGINAL
pointer/raw capacity/layout, not length zero. OwnedPush proves the reserved
push guard is false and retains the allocation through the value write and
length increment. These are typed store/metadata laws. Allocation validity,
byte-heap interpretation, actual type layouts and disjoint owners are STILL
required; Owner is not itself a native heap witness.

## Pinned source and counter type correction

store-source-binding.py checks TWELVE complete Rust 1.94.1 bodies by exact token
streams: push/push_mut, extend_trusted, all four SetLenOnDrop methods, raw capacity,
current_memory, deallocate, RawVec drop and Vec drop. It records the statement
by statement reserved-store/drop correspondence and explicit remaining gaps.
These supplement, not supersede, D572's six complete reserved-append bodies.
The evidence class is a local STRUCTURAL argument, not extraction identity,
machine proof or complete worker association. No fmt always-Ok model is used:
the selected release debug assertion/formatting is disabled.

N90124 emits optimized MIR from an isolated harness including the FROZEN helper
verbatim, rustc 1.94.1, opt-level3, panic=abort, debug/overflow checks off,
r1p-check + ct-host-prover. It CONFIRMS the unsuffixed completed counter defaults
to i32 with public-work-trace disabled. A separately labelled trace-enabled
counterpart infers usize. Original MIR, commands, hashes, stdout/stderr and
receipts are retained. This is compiler type-inference inspection, NOT native
callback execution or a full-crate feature build. Source-to-codegen remains V370.

CounterBounds proves from the ACTUAL SampleDomain34.count/assignments equations
that each valid sumcheck round requests at most14336 items and each family has
width at most896. Its progress and actual_counter_bound justify every reached
positive increment within signed32 range. Commitment widths are at most2/1.
This repairs the counter-type detail of the proposed structural correspondence;
it is not a shipped failure or an unconditional equivalence for unbounded n.
No earlier native worker credit is withdrawn: whole binding was already OPEN.

## Exact remaining work

1. Bind RetainedSpine to the complete deployed host_work.map execution. Connect
   owned allocation descriptors to the real byte heap and layouts; finish
   growing handle push, IntoIter, handle/closure/scope/drop glue, TLS lifetimes,
   native join-late schedule and EVH request/answer/event lowering. Local token
   gates and owner records do NOT discharge this conjunction.
2. Install the SOURCE-BOUND worker at actual opsNative AND reify/thread its
   post-world through the actual capture. NativeBoundary.retained is unchanged:
   op257 is still residual. Sequential64.worker still reuses its input world.
   Its Result(Vec T) signature cannot carry native faults or post-world. Use a
   stateful native capture with partial source projection; do not substitute
   residual fallbacks, .fail or .div for runtime faults/exhaustion.
3. Discharge actual captured callback laws: exact C1/C2 encoders and SemanticOracle
   rows/terminal success at actual round points, then construct actual granting
   execution and Nonempty P. Capture equations, generic grants and op227 equality
   are not the missing success proof. Never use arbitrary successful vectors,
   zero claims, a constant oracle, or a new callback-totality endpoint premise.

V400-257-entry/layout/lowering/callback/answer-timing, V370 and D381/D386 remain
named P obligations. V183 remains SUSPENDED(K-3). rdea-2 exhaustion/panic=abort
branch and N90122 SIGABRT evidence are retained, unchanged and not rerun.
Before/after:V263 OPEN→OPEN;op257 residual→residual;Nonempty P unproved→unproved.
Zero rows/premises removed or added. Three TrustItems, seven links, observer,
simulator and frozen source/ELF pins unchanged. Skeleton consistency: reduced
to non-emptiness. No keys/funds, SBF or ELF work.

## Validation and budget

This continuation15 charged Lean attempts:8 accepted/7 rejected. New accepted
modules:RetainedMethods79948,RetainedSpine79952,RetainedFacts79954,
TrustedStores79956,OwnedDrain79957,OwnedPush79958,CounterBounds79960,
RetainedErase79962. Rejected49/50/51/53/55/59/61 had source/elaboration errors;
changed-source replacements are committed. No unchanged failed source rerun.

Cumulative63/97 Lean charged,35 accepted/28 rejected,34 left,NEXT79963.
Audits79997–79999 UNUSED. Native5/20 charged,15 left,NEXT N90125;0 Kani.
Cumulative Lean wall150.12s,peak4,561,240,064bytes,swap0. N90124 wall0.66s,
peak138,969,088bytes,swap0. Each launch own6G/8G/no-swap/tasks64 scope;
Lean-M7000,one scope at a time,optimized Rust. Cross-job ID checks precede all
new launches. Three quiet-window refusals before79952 were uncharged; each
retried SAME ID after full180s. The lead released the window early by updating
its marker; this job never changed/deleted it. Admission allowed:true+exit0
was checked in each launch shell. No cap increase or memory kill.

Individual receipts and original-module-logs.json.xz retain exact targets,
status,wall,RSS,swap,source revisions/hashes,dependencies and original axioms/
errors. Accepted #print axioms are SUMMARY-BASED and standard only, not a raw,
NEP/coherence/release audit. Failed-source guard unchanged.

Final cache preflight:4300 project objects,9649 direct fingerprints,5673 external
objects,5438 IR companions match;9973 namespace resolutions match,zero links or
copies. Accepted source/object and no-live-own-scope reconciliation passed.
Eight new sources passed the nested-comment-aware forbidden-token/large-term
scan. No full frozen replay while capture is incomplete. No test input excluded
from git and no file over20MB. This is a CONTEXT CHECKPOINT, not completion,
budget exhaustion, impossibility, or a request to approve an unproved premise.
