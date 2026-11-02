# D550 context handoff — native target remains unfinished

Continue ONLY /Users/dominic/ZK/.worktrees/pv-evh, branch
codex/pv-evh-20261029. Same prompt chain and rules. Resume began 6a8a212480;
read RESUME-D550.md for exact established facts and limits. Rows removed NONE.
No delegation, push, crates/programs/soundness/extraction edit, native/Kani run,
or other worktree writes. New Lean modules PV_EVH_. Historical restoration gate
is already cleared; do not reopen it because the old temporary flag is absent.

## Budget, receipts and retained environment

62 charged: 47 accepted / 15 failed. **18 attempts remain. Next fresh 79362.**
Audits 79397–79399 untouched; keep their budget. The 736xx block is retired.
No pending refused/submitted job. 79340's single uncharged refusal was resolved
on that SAME ID after the full cooldown. Read refusal-history if future retries
are needed. Same-shell exit0 AND allowed:true, one scope, 6G/8G/swap0/tasks64,
Lean -M7000. Refusals: full180 seconds, same unlaunched ID, up to ten retries.

Reuse /home/dombarker/project-offloads/codex-pv-evh-20261029 and caches.
Use tools/pv-evh8-20261101/stage.py then compile.py NEW_ID MODULE, source committed
first. Stage now consumes the merged source-binding-extension.json. It is the
SAME runjoin32 project/external cohort; 1,772 added project source/object pins,
zero object conflicts, no library extension. Do NOT rerun the one-time
source_extension.py or native_extension.py to stage consumers. Missing objects
were hash-identical plain project copies in our own overlay; J.json, LEAN_PATH,
shared sources/objects and host infrastructure were unchanged.

First reconcile validation.json / host-final.json / extended-cohort-validation.json
read-only. All accepted source/object/receipt hashes reconcile; no owned scope,
swap, memory kill, limit increase, native/Kani, key/account/funds action or push.
Audit.py is READ-ONLY, never a compiler/manifest replay. No final replay ran.

## Accepted frontier

Strongest entry: PV_EVH_NativeOperatorProver.entry_fixed (79360). It installs
all reified op11/op12 groups (eight source calls) and the retry op233 guard into
RealR1_client.prove_for_proof_accounts at ACTUAL runjoin opsNative and its
heap/box/residual selections. NativeOperators.selection/variant (79354),
NativeOperatorGuard.guard_view (79357), OperatorProver (79355), six Op spines
and OpLeafInstall/OpPrivateSaltsFlow/OpOpeningInstall/OpSaltsProver are accepted.
OperatorSource (79353) relates the actual recorded source bindings.

This remains **P/FinishedView source transport**, conditional on native frame
and remaining leaf compatibility. Native selection is now proved; native
callback/drop/heap/observation fidelity is NOT. Do not confuse these boundaries.

NEW runtime substrate Q has explicit heap/address/owner/backing bytes, handles,
allocator state and errno. Runtime fault is distinct from source failure/div
and exhaustion, retaining full world/events. Partial source projection is NONE
on faults; PartialView is NOT a native adequacy or success/nonemptiness proof.
Runtime (79335), AllocatorWorld (79343), RuntimeOperators (79348),
RuntimeValueBind (79350), RuntimePublishCompact (79351), RuntimeCallbackCtor
(79352), CapacityWorld (79358), RuntimePublishInstall (79361) are accepted.
The publication adapter installs STATEFUL allocation and op12 under a partial
view, including allocator-failure worlds. Pure source-value/global FinishedView
must not be reinstated for native capacity: ViewBoundary (79331) remains valid.

## Exact next work

1. Native heap and runtime-fault fidelity: bind Rust 1.94.1 RawVec/allocator
   branches from allocator-sources.json statement by statement (own-1).
   layoutFor's element size/alignment/padding/maxBytes are NOT yet bound to
   native metadata. ValidAnswer is NOT proved. Physical backing bytes do NOT
   imply initialized regions. Prove an owner/identity-indexed source/native
   state abstraction, including which backing block each extensional source
   Vec denotes, stack/borrow restoration, handles and errno. No hidden success
   assumption, no pure-value allocator, no new T field.
2. Bind allocation-failure/overflow diagnostic and abort/panic handlers under
   fmt-1. CapacityWorld's diagnostic lists are explicitly unbound inputs;
   their preservation does not prove native handler fidelity. Relate the
   runtime allocator world to actual runjoin Heap/Box requests. Keep ALL fault
   prefixes and distinguish native faults from exhaustion and source div.
3. Install RuntimeCallbackCtor's seven frames through RuntimeOperators at the
   proved actual NativeOperators selection. Inspect/bind real argument/capture
   drops, unused closure drop, unwinding, zeroization and partial entropy-fill
   failure cleanup; constructor Result purity proves no native drop silence.
   P's global FinishedView frame assumptions still cannot cover runtime faults.
4. Extend Q/partial source transport through the full entry and bind every
   remaining native path/digest/options, hash/oracle bytes, source primitive,
   formatting and failure/mutable restoration operation. Embedding P into Q
   while leaving its heap untouched is NOT native heap fidelity. Do not
   rebuild accepted predecessors merely to test a new consumer.
5. ONLY AFTER full native adequacy: prove unchanged oraclePrefix/countTrace
   and nonce-store fileTrace projection links, including all reached leaf
   events. D520/U/D524 client/account fields stay named inputs. No client
   reference/port/opaque plan::prove workaround.
6. ONLY AFTER actual-family/provenance-fixed links: (v') consistency reduces
   to a successful actual worldRun at opsNative AND its allocator world.
   NativeObstruction62/op132 still prevent inferring uniform success. No
   unrelated MODEL witness, implicit success domain, or T-field addition.

No WIP Lean source awaits retry. Failed source IDs and replacements are detailed
in RESUME-D550.md and retained receipts. Last failed 79359 was replaced by79360;
79361 is accepted. Keep native_preflight.py --require-native-closure failing
while the explicit native boundaries remain open, even though revised Op
spines have no latent external lifts. All new generators have --check and are
included in audit.py. Run final compiler axioms/closure/manifest once only when
native acceptance is actually ready. This checkpoint is not completion,
budget exhaustion, a host blocker, or a checked counterexample to shipped Rust.
