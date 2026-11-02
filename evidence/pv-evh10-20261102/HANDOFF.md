# D551 context handoff — native target unfinished

Continue ONLY /Users/dominic/ZK/.worktrees/pv-evh, branch
codex/pv-evh-20261029. Baseline d88f951fd4725367ea93b58fb09f8ddc37856ca4.
Read the prompt-pv-evh9.txt chain and inherited EVH8 handoff. No delegation,
push, frozen Rust/extraction/soundness edits, native/Kani runs, other worktree
writes, wallet/key/account/funds actions or T-field changes. Rows removed NONE.
This is a CONTEXT checkpoint, not completion, budget exhaustion, host blocking
or a checked counterexample against shipped Rust.

## Budget and exact restart

D551 used **18 charged attempts: 13 accepted / 5 failed**, IDs 79362–79379.
The 18 inherited attempts are fully used. **82/100 remain. NEXT FRESH 79500.**
79380–79396 were not used; do not infer another 17 inherited attempts from
those unused numbers. Both audit triplets 79397–79399 and 79597–79599 untouched.
No compiler audit/manifest replay ran. No job is pending and no owned scope
remains. One uncharged admission refusal on 79362, then accepted SAME ID after
the full cooldown. A local early retry was stopped by the wrapper's cooldown
assertion BEFORE any host admission/submission; no void compile resulted.

Receipts now: evidence/pv-evh10-20261102/. Use ONLY:

    python3 tools/pv-evh10-20261102/stage.py PV_EVH_NewModule
    python3 tools/pv-evh10-20261102/compile.py 79500 PV_EVH_NewModule

Commit source before stage/compile. Same retained host workspace and SAME
runjoin32 project/external cohort. stage.py consumes EVH8's merged extension
and all accepted EVH4/5/8/10 receipts; do NOT rerun provisioning/extension
scripts. Own wrapper adds the new range, budget and inherited-first checks;
no host infrastructure, J.json, LEAN_PATH or library authority changed.
Guard hash is recorded in validation.json. Same-shell admission requires exit0
AND allowed:true; one 6G/8G/swap0/tasks64 scope, Lean -M7000, no cap increase.
Refusals: full180 seconds, same unlaunched ID, up to ten retries. Preserve
source-only failed-source guard and pre/post-submit transport rules.

## Accepted local results and their limits

- HeapOwnership 79362: explicit owner/allocation key, extensional initialized
  prefix distinct from backing capacity, identity uniqueness and restoration
  of the same owner/address/layout. These are STATE RELATION laws, not native
  stack/borrow fidelity or proof that actual callers meet the relation.
- AllocationOwnership 79363: ValidAnswer implies a fresh unique heap and an
  owned EMPTY initialized prefix on allocation; old owners survive success or
  denial. ValidAnswer itself remains unproved for the actual allocator.
- VolatileClear 79365: one byte store per initialized element followed by ONE
  final fence; preserves physical identity/address/layout and spare backing.
  This models the PROJECT volatile_clear shape only, NOT zeroize's array glue.
- HeapClear 79368: lookup by owner AND identity; missing key or oversized
  initialized prefix faults. Successful clear retains store/fence events,
  allocator state and errno; unrelated keyed blocks remain unchanged.
- LayoutRepeat 79369: checked multiplication and aligned isize size limit are
  separate checks; the earlier CapacityWorld layout agrees when metadata is
  already padded and the max-size bound fits usize. Native padding bitmask,
  actual type sizes/alignments/width and valid metadata still need association.
- EntropyCleanup 79371: original buffer cleanup runs on an ordinary fill Err
  using the FULL post-fill world (partial writes retained); cleanup faults
  retain both prefixes; abort skips cleanup. These are generic frame laws.
  Its dropEntropyBuffer helper uses project single-fence clearing and MUST
  NOT be installed as zeroize::Zeroizing array glue. Use ZeroizeArray instead.
- ClientAllocator 79372: System denial produces immediate abort inside the
  allocator, before returning a null pointer to std's diagnostic handler.
  Preserves heap, errno, allocator and all supplied external abort events.
  Actual System/native allocator selection and ValidAnswer remain open.
- LiteralDiagnostics 79373: exact error/panic REQUEST bytes from adopted
  diagnostics.rs, returned io::Error drop effects and writer fault prefixes.
  Request equality does NOT imply delivered bytes/state/timing independence.
- WriteAll 79374: finite runtime loop retains short-write suffixes/post-state,
  interruption/error inspection and destruction, write-zero construction,
  bad-count panic, exhaustion and fault prefixes. Driver leaves are OPEN.
- ZeroizeArray 79375: zeroize 1.9.0's scalar volatile store plus optimization
  barrier PER ELEMENT, distinct from project final-fence clearing. Its
  entropyFill uses the original key and a 64-byte cleanup after partial error.
  Native stack mapping and per-element address/barrier association remain OPEN.
- ClientRuntimeFault 79376: capacity panic runs the fixed hook then abort under
  the adopted profile; hook faults retain prefixes and do not unwind.
- OwnedCapacity 79378: constructor returns a source Vec AND its storage key;
  successful allocation installs empty-prefix ownership, zero-size allocates
  nothing. This is NOT installed into the actual entry. Do not discard storage
  and claim extensional Vec identity suffices for later native operations.
- OwnedCapacityFaults 79379: allocator denial retains fault/world/prefix and
  has no source Result; overflow retains a hook fault's full prefix.

All thirteen modules are accepted; NO uncompiled Lean WIP remains. Every added
theorem has a successful printed axiom result, subset of propext/Quot.sound
(or empty). Failed attempts 79364 (implicit List.take_left arguments), 79366
(reserved matches identifier), 79367 (record continuation syntax), 79370
(over-unfolded bind projections), 79377 (simp produced True) were replaced by
changed proof bytes 79365/79368/79371/79378, with all failures retained.

## Source evidence and adopted diagnostics

native-sources.json is READ-ONLY source evidence, NOT completed own-1 binding.
It pins Rust 1.94.1 RawVec/Global/Layout bodies, zeroize1.9.0 array/iterator/
scalar/Zeroizing bodies, project clearing and 64-byte entropy error source.
Client diagnostics are read from pv-uc at fixed
9917a5b8df742db3c7ca4c1c080e6a0ef1a8f5b6, byte-equal the D474(C) source freeze
d42f8a4db548bccd06e15bcd64c9fd98abe423a9. User D551 supplies adoption authority;
the historical draft REPORT still says NOT ADOPTED and is not current authority.
No other worktree was written or client port/extraction substituted.

D474(C) error/panic requests are client error\n and client panic\n. The custom
allocator delegates System alloc/alloc_zeroed/realloc and ABORTS ON NULL before
std's dynamic allocation-size formatter. Deallocation delegates System.
An initial DESIGN note incorrectly suggested the default OOM formatter must
remain on this route; source inspection corrected it before the diagnostic
models. Do not reinstall legacy std numeric OOM diagnostics here. Fixed literal
REQUESTS still need faithful stderr partial/error delivery and io::Error drop;
no Aeneas.Std Unit fmt credit. External process abort/crash remains observable.
Hook installation, backtrace initialization and actual profile selection must
be bound, not inferred from these local control laws.

## Next concrete work (still the native frontier)

1. Bind native metadata/padding and RawVec/Global/client allocator source
   branches statement by statement under own-1, including native address,
   errno and allocator state. Prove actual ValidAnswer. OwnedCapacity's source
   Vec and token must propagate through actual consumers, not be separated and
   then re-associated by contents. RuntimePublishInstall still uses the old
   unowned CapacityWorld: new constructor is NOT integrated there yet.
2. Add actual stack/initialized-region/borrow restoration and retired-memory
   abstraction. State.heap currently records ALLOCATOR blocks; treating the
   entropy stack array as one of them without proof would be false fidelity.
   Native initialization/partial writes and deallocation must retain L3 data;
   removing a block is not proof that freed bytes were zeroized.
3. Inspect/bind actual argument/capture/unused-closure drops, seven concrete
   RuntimeCallbackCtor frames and zeroize/disposal on success/Err/abort. Install
   them through RuntimeOperators at proved NativeOperators selection. Current
   OperatorProver entry is still P/FinishedView source transport. Generic drop
   and clear laws are not native drop evidence. Zeroization is L3, never silence.
4. Bind literal writer/syscall/error/drop leaves and the adopted client
   allocator/hook/profile. Generic Writer/Driver can still return source
   fail/div: a global .ok-vector PartialView for a panic handler is NOT justified
   by these interfaces alone. Bind actual native terminal behavior rather than
   silently adding a handler-success hypothesis or erasing failures.
5. Extend Q through the full proof-account entry and all remaining path/digest/
   options/hash/oracle-byte/primitive/failure/mutable restoration operations.
   Then, ONLY after full native adequacy, prove unchanged oraclePrefix,
   countTrace and nonce-store fileTrace links over provenance-fixed actual
   families. D520/U/D524 client/account fields remain explicit inputs.
6. ONLY then reduce (v') consistency to nonemptiness of successful actual
   worldRun at runjoin opsNative AND allocator world. NativeObstruction62/op132
   remain; no uniform success or unrelated MODEL witness is available.

## Verification and checkpoint

Initial inherited EVH8 read-only audit PASS reconciled 62 receipts and the
extended cohort. EVH10 audit.py PASS reconciles all 18 new receipt/source/object
hashes, exact IDs/budget, caps, axiom sets and source inventory; no scopes live.
validation.json and host-final.json are retained here. Native preflight with
--require-native-closure STILL FAILS intentionally on the open boundaries.
No full compiler audit, closure/manifest replay or privacy completion is claimed.
Max RSS 2,609,696 KiB; max wall 0:03.58; swap0 throughout. No memory kill or
limit increase. No native/Kani/key/account/funds action or push.

Before/after: ALL endpoint/deployment/privacy rows unchanged. New relations,
stateful constructor/cleanup/diagnostic laws are local proof progress, not
native adequacy. V370/V371, rdea-1/V400, D159/D166, L1/L2/L3 and client inputs
remain retained obligations. T remains exactly its existing three fields.
