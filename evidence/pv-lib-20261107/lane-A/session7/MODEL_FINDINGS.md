# Session7 — partial source-action repairs; completion NOT established

Base03c3c72b1436a3cd5677265b0682a9490a4f4878. The accepted D989 inventory is
unchanged. No ledger/package/row-consumer/implementation/frozen-spec changes.
No endpoint premise removed/added, no T field, no slot status change.

## Cell504

CellSetBegin implements the documented replacement boundary from pinned
core/cell.rs433–438 and retains OLD T and its actual type/Destruct witness.
CellSetMetadata checks all six EXACT raw call tokens, not only function id504.
CellSetThreadId additionally uses pinned std/thread/id.rs: ThreadId derives
Copy, so Option<ThreadId83> has a trivial selected payload destructor. No
arbitrary Option<T>, arbitrary-T no-destructor premise or identity delta is
introduced. Four emitted specializations417/437/477/629 have a complete local
source-store projection and exact whole-reply delivery on every answer.
The source read/address/representation facts still need caller discharge.

SpawnHooks602 and generic762 remain nontrivial. SourceReplies7's
nontrivial_still_unsupported checks that the new partial model is undefined
even when their replacement prefix is defined. This is a model gap, NOT a
counterexample to frozen Rust or a proof of original-entry reachability.
CellSetBegin's saved old value is a necessary start transition, not a complete
old-T destruction implementation. No caller history is promoted through it.

## Last-reference destructors

WeakDropSource/WeakDropBranches replace the source-only nonlast restriction
with a decrement phase, raw usize::MAX dangling branch, and a retained
last-reference deallocation tail. Pending leaves the source block live and
does not decrement again. Successful source-root completion invalidates that
root; every failure/div/fault/pending branch uses the pinned full reply rule.
This is SOURCE lifetime support, not complete OWNER allocator/registry,
physical-memory/order or OWNER-only backing adequacy.
Last-strong486 payload Drop, drop_slow584's guard, all nested source effects
and source/OWNER deallocation correspondence remain unbound.

## Wrapper and typed-body route

ThreadCloneStore names214's source-backed Thread -> Pin -> Arc -> NonNull
pointer path and SAME strong-count increment/overflow prefix as Arc clone.
It does not certify OWNER-only backing or the native returned value/world.

The generator reuses the UNCHANGED pinned converter functions at
3eae57e2a2cdf6be5eb06ab8b45e7df7c5bf1404 on the accepted N95808 input.
EMITTED_BODIES.json records exact raw/output hashes. Eight emitted bodies
486/584/608/214/168/122/128/14 can be rendered without deleting any cleanup.
This is syntax support, NOT a proof of their native whole effects. run_spawn_hooks454
still fails conversion at a cleanup Match (KeyError SwitchInt); collect4 is
opaque. No replacement program for either was invented. Pin311, join's nested
calls, TLS/parker and callback source effects still need exact named bindings.

TypedDropSource provides source-body dispatch specifically for SIZED emitted
SpawnHooks glue608, preserving the actual source parent, store and full native
subcall paths. EmittedDropBinding supplies608 by its exact retained program.
This does NOT resolve arbitrary UntrackedDestruct, type substitution, opaque
nested drop_in_place248, or the complete nonempty SpawnHooks/Arc chain.

## Pending phases and the import surface

Import PV_LIB_A_StoreActionTable to retain PV_LIB_StoreActionTable.v2 unchanged.
Import PV_LIB_A_StoreActionTable7 for PARTIAL v2Source and named fixed meanings.
The latest source-dispatch candidate is TypedDropSource.step (with the explicit
608 resolver binding), extending DeferredActions.step over Table7's state.
It is not a complete MachineSpec/native adequacy assertion.

ActionPolling and the intermediate Table7.sourceStep retain applied writes on
pending, but are NOT correct standalone polling models for reply-dependent
CAS530/555 or Vec push167/append10: completion would skip their deferred write.
Their mathematical graphs remain retained. DeferredActions.step corrects these
four by re-evaluating their exact named meanings; pending_start proves that no
source write has been committed on their pending arm. All other applied
prefixes and the last-Weak completion tail retain their phase. Failure, spurious
weak CAS failure, overflow-sensitive prefixes and all original answers remain
visible. No source transform is supplied by a caller.

## Requested ordering and remaining result

The three requested adequacy gaps are NOT closed. Accordingly Range93, f6 and
OwnInit corrected-machine histories were not attempted/promoted out of order.
All170 inherited slot records remain unchanged (118 qualified INSTANTIATED,
35 MISSING,12 WAITING,5 SPEC-ERROR). Named graph identities, successful imports
and an axioms audit are not source adequacy or privacy closure.
