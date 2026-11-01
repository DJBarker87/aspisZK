# D545 EVH8 handoff — full native task remains unfinished

Continue ONLY in /Users/dominic/ZK/.worktrees/pv-evh, branch
codex/pv-evh-20261029. Baseline 0da088f6f87a20db01518eb53c95e2343f7b47bf.
Same prompt chain/rules; no delegation, push, crates/programs/soundness edits,
extracted-source edits, other worktree writes, native or Kani runs. New modules
PV_EVH_. Receipts evidence/pv-evh8-20261101/. **Rows removed NONE.**

## IDs / budget / host

Charged 32 attempts: 22 accepted,
10 failed; 48 of 80 remain.
Focused 79300–79396; audits 79397–79399 UNUSED. The 736xx block is retired.
Next fresh ID 79332, UNUSED. All prior admission-only refusals were resolved
on their same IDs after the full cooldown. There is no pending launch/refusal.
Retry SAME ID only after FULL 180-second cooldown from latest refusal epoch;
up to ten retries. Read refusal-history files to count. Never bypass admission.
Same-shell exit zero AND allowed:true, one scope, 6G/8G/swap0/tasks64, -M7000.

Reuse /home/dombarker/project-offloads/codex-pv-evh-20261029 and all caches.
Own stage/compile/audit tools under tools/pv-evh8-20261101/. No host infrastructure
changed. Current stage snapshots can be reused on admission-only retries when
source/dependencies have not changed. A new accepted dependency needs staging
for its consumer, not rebuilding predecessors. All imports remain in the
inherited coherent project/external cohort; no library extension.

The historical restoration gate is ALREADY CLEARED, despite the removed temp
flag. Committed pv-evhd/rules.json records reading the flag and its hash/size;
pv-evh5/resume-D540.json already recorded its later absence with explicit resume
authorization. restoration-resolution.json records this evidence. Do not create
another bootstrap hold or treat a missing asynchronous owner answer as approval.

## Accepted work and its exact scope

OpeningInstall.install_fixed and OpeningProver.entry_fixed install the source
PrepareOpening / FinishOpening / PublishCompact spines into the actual extracted
RealR1_client.prove_for_proof_accounts entry. PublishCompact exposes the source
Vec.with_capacity let as an effect-capable native leaf; ValueBind's generic
law is axiom-free. Allocation failure is not erased or assumed source-success.
All sixteen prepare / thirteen finish / fourteen publish leaves remain native
obligations, including the capacity leaf. This is Result transport, not native
trace adequacy.

NonzeroStep / NonzeroFlow interpret the actual entropy_nonzero32 source loop,
without a whole-helper answer. NonzeroInstall / NonzeroProver install this same
interpreter at the outer nonce guard and the inner entropy-block checks. The
remaining entropy structure has six native leaves. NonzeroSafety (79319)
proves the active array read is bounded, increment cannot wrap, source step is
total, and step interpretation equals the source-primitive lift. Generic scalar
proofs; no concrete 32-byte normalization. NonzeroTotal (79323) proves the whole interpreted loop completes with enough
fuel; run 33 terminates with unchanged world and [] events for EVERY typed
32-byte input. Source totality follows from exact erasure. No concrete-byte
normalization, extra runtime-success claim or limit increase was used.

PrivateSaltStep (79314) and PrivateSaltsStep (79317) are accepted source spines.
PrivateSaltsStep required distributing a match continuation and then normalizing
ONLY the source Result bind association. The generator permanently emits that
proof. PrivateSaltsFlow (79324) / SaltsProver (79328) are ACCEPTED. The latter is the
strongest accepted entry. It still has remaining native leaf/runtime premises.

All accepted axioms are standard or empty; per-ID receipts record revision,
blob/SHA, dependency fingerprint, target, exit/wall/RSS/swap and printed axioms.
All jobs stayed below cap, swap zero, no memory kill or limit increase. Refusals
were uncharged. Source failures and changed replacements are retained.

## Important native gap found (do not lose this)

In the actual loaded extraction, core.result.Result.map aliases ExternalFuns.op11
and map_err aliases op12. The old generator's language-level lift whitelist
therefore hides native operator/callback/drop obligations. This does NOT refute
accepted Result transport, but prevents promoting entry_fixed's Compatible
hypotheses to full native coverage even if those hypotheses are discharged.

native_preflight.py (--check) permanently inventories SEVEN such lifted sites
in the selected source spines and says native coverage OPEN. --require-native-closure
fails while any remain. Native callback purity alone does NOT bind the external
operator! entry-open-native-leaves.json gives 109 explicit fields PLUS these
aliases and runtime/boundary obligations; it is a TEXTUAL census, not coverage.

PrivateSaltWrap (accepted 79326) defines an independently interpreted pure newtype
constructor/map. Its map_fixed/map_agrees require an EXPLICIT sourceMap op11
installation; actual opsNative association remains OPEN. Its Rust constructor
body is byte-identical across extraction/current source and is just Self(values),
with no allocation in that body. Later vector drop stays OPEN.

ResultOps (accepted 79327) gives source op11/op12 models and native event operators
with explicit eventful callbacks and unused-closure drops. Callback semantics
owns consumed capture/argument drops and unwinding. It proves Result transport
only under its explicit dictionary selection, callback FinishedView and silent
successful-drop view. It does NOT prove actual dictionary/native adequacy.

VariantGuard (accepted 79329) gives the three-constructor comparison and event-free
retry guard at an explicit op233 dictionary. Actual opsNative installation is
OPEN. Existing source value definitions are ProverRwCallerBinding.variantEq,
ProverRwSuccessOptions.resultMap, and PDict_RejectionStdSource.core.result.Result.map
(read through git show only; not imported, no cohort substitution). Reuse their
actual source bindings when available; do not credit a fresh model dictionary.

## Crucial source-view/runtime-fault boundary

ViewBoundary (79331) proves failure_excludes_value and
capacity_failure_excludes_compatible: if a native capacity handler finishes
with .fail in ANY world, it cannot satisfy the old global FinishedView against
the pure source Vec.with_capacity value. This is a checked limitation of that
view, NOT a counterexample to shipped Rust or the stateful-native task. Do not
claim all native conditions discharged by silently excluding abort worlds.

The full native outcome model needs runtime faults and their retained prefixes,
with an explicit domain for source Result projection (or an equivalent proved
partial-view relation). Do not conflate a native abort with finite fuel
exhaustion or source divergence. This is in addition to the known absence of a
uniform dictionary view for advancing reject-then-success entropy.

CallbackCtor (79330) has seven concrete source callback frames. Every one runs
its typed dropArgument and dropCapture computations before the constructor,
so their state/events/failure/exhaustion survive. Their actual native drop
bindings remain OPEN. callback_frontier.py identifies EIGHT actual operator
calls (seven unique spine/operator groups); callback_ctor.py --check reproduces
the exact source-body laws. Source callback bodies alone do not prove their
implicit native drops or actual op11/op12 selection.

## Exact next proof actions

1. Start fresh 79332. All new Lean modules are now accepted; no WIP Lean file
   needs a rerun. Read validation.json and reconcile the retained host first.
   There are 48 attempts left; all three audit IDs remain unused. This handoff
   is a CONTEXT CHECKPOINT, not completion, budget exhaustion or a host blocker.
2. Wire ResultOps and CallbackCtor through the seven lifted spine/operator
   groups (eight calls), instead of executing their Result first. Prove actual
   opsNative op11/op12/op233 bindings, reusing the selected native source/value
   bindings where available. Native helper callbacks/drop laws may emit events:
   FinishedView alone never proves their projections empty. The operator/frame
   laws currently compile but are NOT yet installed through the entire entry.
3. Make runtime-fault/source-view domains explicit as above. Supply actual
   allocation/heap/capacity/handle/address/errno state and native associations,
   or prove a valid state abstraction. Current World has only file/oracle and
   counter data, not an already-proved heap/handle model. Native allocation
   success, failure, ownership and identity must not be hidden in a new T field.
4. Bind remaining native effects: zeroize/drop (including partial entropy-fill
   failure cleanup), paths/digests/options, hash/oracle bytes, checked failures,
   panic/abort and EVERY reached formatting path under fmt-1. Preserve every
   mutable-borrow restoration and account for memory effects on error paths;
   merely preserving source tuple/function syntax is not native heap fidelity.
   No whole-helper OS answers. Source Rust bodies / Std drops must be inspected
   and bound, not inferred silent from their Result values.
5. Only AFTER full native coverage: unchanged oraclePrefix, countTrace and
   nonce-store fileTrace projections. D520/U/D524 client/account inputs remain
   explicitly named. No client reference, opaque plan::prove or alternate port.
6. Only AFTER actual-family/provenance-fixed links: (v') reduce consistency to
   successful actual worldRun at runjoin opsNative AND its allocator world.
   NativeObstruction62 and op132 still prevent inferring uniform success. No
   unrelated MODEL witness earns credit. No new T field or source/native trust.

Use tools/pv-evh8-20261101/stage.py then compile.py NEW_ID MODULE, source
committed first. Do not rebuild accepted predecessors or mix cohorts. The
wrapper's failed-source guard hash is in validation.json. Refusal retries use
SAME unlaunched ID after FULL 180 seconds, up to ten; proof failures require
changed proof bytes. Source failures 79307/08/12/15/16/18/20/21/22/25 and their
replacements remain in receipts. All accepted source/object/receipt hashes
reconcile; no live owned scope, memory kill, cap increase or transport failure.

Native inventory/preflight is TEXTUAL and still OPEN. Its --check means exact
inventory reproduction, never native acceptance; --require-native-closure fails
while aliases remain. audit.py includes every generator/callback/preflight check.
Run the one final axioms/closure/manifest replay only after actual native
acceptance is ready, not for this incomplete frontier. No native/Kani,
wallet/key/funds operation, push or release claim occurred. Rows removed NONE.
