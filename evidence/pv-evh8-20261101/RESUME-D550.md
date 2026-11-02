# D550 continuation — source operators installed; native task unfinished

Resume baseline 6a8a212480; same worktree and branch. Rows removed NONE.
This is a context checkpoint, not completion, exhausted budget, a host blocker,
or a counterexample to the shipped native prover.

## Established and retained boundaries

Six new Op source spines replace all seven unique lifted operator groups
(eight actual calls) by computations BEFORE evaluating their source Results.
Accepted: OpPrivateSaltStep 79332, OpMaterialFromEntropy 79333,
OpApplyMaterial 79336, OpPrivateSalts 79337, OpPrepareOpening 79338,
OpPublishCompact 79339. OperatorFrames 79334 retains invoked callback and
unused-closure-drop computations. OperatorInstall 79340 supplies the six
adapters, without assuming non-operator leaves have native coverage.

OpLeafInstall 79344, OpPrivateSaltsFlow 79345, OpOpeningInstall 79346 and
OpSaltsProver 79347 recompose the actual extracted entry. OperatorProver
79355 installs the frames in it. NativeOperators 79354 proves op11/op12
selection AND op233 equality at ACTUAL NativeResidual62.opsNative, for its
base/heap/box/residual ops. NativeOperatorGuard 79357 installs its retry guard.
NativeOperatorProver.entry_fixed 79360 installs these selections in the
extracted proof-account entry. OperatorSource 79353 reuses and relates actual
ProverRwSuccessOptions.resultMap, ProverRwOuterMapErr.map_err and
ProverRwCallerBinding.variantEq. No fresh model dictionary earns credit.

**These are source Result-transport/selection laws, not native event adequacy.**
NativeOperatorProver still needs native invocation/drop and remaining leaf
compatibility. Its P/FinishedView interpretation cannot account for allocator
abort worlds; do not promote it to the complete native runtime producer.

Runtime 79335 adds explicit heap blocks/ownership/address/backing bytes,
handles, allocator state and errno. Runtime fault, returned source Result and
finite exhaustion are distinct. Fault bind retains the final state and prefix;
its source projection is NONE. PartialView composes only where projection is
defined and proves neither nonemptiness nor native adequacy.

AllocatorWorld 79343 takes the complete WORLD into allocator answers, updates
allocator/errno even on failure, preserves heap on denial, and installs a fresh
identity/address/backing block on success. RuntimeOperators 79348 retains
callback/unused-drop faults, RuntimeValueBind 79350 supports effectful source
values, RuntimePublishCompact 79351 interprets the actual publication spine in
Q, and RuntimeCallbackCtor 79352 gives seven typed concrete callback frames.
CapacityWorld 79358 includes layout overflow, zero allocation-size, successful
allocation and allocator-fault branches. Its failure theorem retains allocation
request/denial plus diagnostic prefix, heap and errno; sourceProjection is NONE.
RuntimePublishInstall 79361 installs this capacity leaf and eventful op12 in
publication with a PARTIAL source view, not an impossible global value view.

## Native heap/fault limits (explicit, NOT discharged)

AllocatorWorld.ValidAnswer is a defined P obligation, not an accepted allocator
contract. Backing bytes do NOT prove Rust initialization or safe reads.
Identity/address/owner metadata are retained but their native vector/stack/
borrow/alias abstraction is not proved. Subsequent source Vec values are
extensional and alone cannot select the correct backing block among equal
values. LayoutFamily/element metadata, padding, isize limit and native layout
checks remain source-binding obligations. Runtime State handles are data only.

CapacityWorld returns the source vector projection AFTER its world computation;
that is not proof of native ownership/handle fidelity. Allocation fault and
overflow diagnostic lists are explicitly unbound model inputs: no fmt-1 or
abort-handler association has been established. No runtime-success world is
excluded by the partial-view law, but fault runs have no source projection.

Runtime source inventory allocator-sources.json records hashes and selected
Rust 1.94.1 RawVec/alloc bodies. It is read-only source evidence, NOT a completed
own-1 structural binding. RUNTIME-DESIGN.md was committed before runtime code.
All native heap/drop/zeroize/cleanup, formatting, path/digest/options, hash/
oracle-byte and primitive/error-path associations remain P work. In particular,
there is no proved relation from State.allocator to runjoin's Heap/Box requests.

## Cohort, failures, validation

All sources compiled only on retained host, one admitted 6G/8G/swap0/tasks64
scope, Lean -M7000; same-shell admission exit 0 AND allowed:true. 79340 had ONE
uncharged refusal, then passed on SAME ID after full 180 seconds. No pending
submission/refusal or owned scope remains.

New source failures retained: 79341 allocator record syntax/ambiguous bind;
79342 redundant terms after simplification; replacement 79343. 79349 ambiguous
runtime bind; replacement 79350. 79356 ambiguous runtime lift; replacement
79358. 79359 illegal section-local dictionary instance; replacement 79360
uses letI inside the entry/function type. All replacements changed proof bytes.
No kill, cap increase, swap, native run, Kani, key/funds operation or push.
Two pre-compiler staging corrections are uncharged: OperatorProver staged
before its commit completed, and extension code initially rejected inherited
namespaces rather than reusing their first-root objects. No Lean was submitted
for either. Source extension initially found symlinks and converted only own
project-overlay objects/companions into hash-identical plain copies under h6.

source-binding-extension.json now verifies 1,772 additional project modules in
the SAME existing runjoin32 cohort. NativeFrames62 cone probe found ZERO object
conflicts. native-binding-extension.json records 845 added projects and 236
plain file copies; source-binding-extension retains the earlier 927-project
source selection closure. No library authority, J.json/LEAN_PATH, shared source
or shared object was changed. Stage.py consumes the extension, verifies object
hashes/effective first-root resolution and checks source changes since its pin.
Do not rerun the one-time source_extension.py/native_extension.py provisioning
scripts to stage a consumer: use stage.py, which retains the merged manifest.

Read-only audit.py PASS: all 62 receipts/source/object hashes reconcile,
standard-or-empty printed axioms on accepted jobs, no owned scopes. It checks
all new generators and the extended cohort. Native preflight distinguishes
legacy lifted aliases from reified Op spines, while --require-native-closure
still FAILS by design on the named native boundaries. That failure is not a
release replay or a counterexample. No final compiler audit/manifest replay ran.

Budget: total 62 charged, 47 accepted / 15 failed. D550 used 30 attempts,
25 accepted / 5 failed. **18 attempts remain. Next ID 79362.**
Audits 79397–79399 untouched. Reserve the final audit/replay budget.
Exact per-target revision/blob/SHA, dependency fingerprint, wall/RSS/swap,
exit and #print axioms are in receipt-ID.json. Compiler guard hash unchanged.
