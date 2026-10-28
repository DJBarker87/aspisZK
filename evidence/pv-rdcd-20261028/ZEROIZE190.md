# zeroize1.9.0 source association for V221/V222

RESTORED at the original emitted byte-dictionary/source-law boundary, class C, evidence class **structural (K-1 substitute)**. This is not a whole-client, compiler-correctness, deployed-binary, native RunJoin or privacy-headline closure. The native finite checks are supporting validation, not universal execution proofs.

## Before and after

Before: zeroize1.8.1's byte blanket instance was associated with `volatileWrite(address,0); compilerFence(SeqCst)`, once per byte, with unchanged surrounding memory and frame. That exact effect trace is not the1.9.0 source.

After: zeroize1.9.0 performs `volatile_write(self, u8::default()); optimization_barrier(self)`. On the deployed x86_64/non-miri selection the barrier is `asm!("# {}", in(reg) core::ptr::from_ref::<T>(val).cast::<()>(), options(readonly, preserves_flags, nostack))`. The new source event is `asmReadBarrier(address)`, following each volatile zero write. The old proof files are unchanged; new PV_RDCD modules state the replacement law.

The marker dictionary is the actual emitted `U8.Insts.ZeroizeDefaultIsZeroes`; the array dictionaries in the frozen FullFuns use lengths32/64. The unchanged original census script is replayed in `zeroize-census/`, with its complete source and inputs in `zeroize-census-inputs.json`. No claim for arbitrary user-defined Default/Zeroize implementations is inferred. Mathematical array laws generalize over N, while native restoration here covers the retained emitted byte instances.

## Structural source cone and proof

`zeroize190-complete-structural.json` checks26 complete bodies/invocations in13 actual1.94.1 core / zeroize1.9.0 source files, retaining full file hashes and texts. `structural-zeroize190-complete.py` is explicitly a revised1.9 binding, not a replacement passed off as the old checker. The original checker is separately replayed unchanged in `original-gates-recovered/results.json`, where it rejects1.9.0's changed Drop/body expectations.

The concrete cone is:

1. `Zeroizing<[u8;N]>::drop` delegates once to array Zeroize; byte-array field glue has no user destructor or allocator action. The added trailing semicolon preserves the Unit result (`ZeroCursor.drop_semicolon`).
2. Array Zeroize coerces to a slice and constructs `slice::IterMut<u8>`. Slice length/metadata, NonNull construction/cast/as_ptr, raw pointer add, NonNull equality/add/as_mut are checked against the installed core sources. `IntoIterator` is identity, and Iterator for `&mut I` delegates next once.
3. The non-ZST next branch compares start/end, advances start by one before yielding the old exclusive reference, and returns None at end. `ZeroCursor.next_live`, `next_empty` and `source` prove its address-projected recurrence equals the owned index recurrence for the valid byte slice's exact length. No mixed front/back model is used.
4. The byte blanket Default is literal0. `volatile_write` reaches `ptr::write_volatile` and `intrinsics::volatile_store`; the assembly operand reaches from_ref and a raw-pointer cast. Debug-only add checks are inactive in release. The volatile-store alignment precondition is satisfied by valid exclusive u8 references. No allocation or dependency callback is reached in this concrete cone.

Primitive interpretation remains Rust's valid-reference/provenance and array-layout rules, pointer metadata, address-preserving casts/transparent NonNull representation, in-allocation/one-past offset, primitive pointer comparison, volatile store, and inline assembly semantics. `ZeroCursor.casts` is an address-projection theorem, not a mechanized Rust provenance or compiler theorem. The source association is structural, with these primitive semantics stated explicitly; it is not promoted to a whole-machine theorem. The earlier by-name MIR envelope includes unrelated LinkedList/BTree/Simd alternatives; those are not concrete callees of this typed cone.

`PV_RDCD_ZeroWorld` proves full overwrite, preservation outside the target, unchanged arbitrary frame and allocator/framed-drop counters, exact write/barrier counts, and source/reference caller composition. `ZeroTrace` proves the exact ordered source history. `ZeroSelected`, `ZeroConsumed` and `ZeroDrop` prove complete Result equations for the exact emitted dictionaries and consumed destructor, retaining every updated element. No mutable-iterator Aeneas emission is credited. The13-module private closure was built in dependency order; audit41497 and focused replay41498 pass with standard axioms only.

## Meaning for privacy

Volatile stores retain their Rust observable-effect status. The assembly is neither `pure` nor `nomem`: its compiler interface permits reads through the passed pointer but promises no writes to external memory. Its comment-only template has no memory-writing instruction. `readonly` is not a general read/write memory clobber, a SeqCst compiler fence, a hardware fence or inter-thread synchronization. It does not establish identical ordering constraints for arbitrary surrounding atomic/memory operations. See the [Rust Reference](https://doc.rust-lang.org/reference/inline-assembly.html#options); the versioned1.94.1 HTML was unavailable, so operational checks use the pinned installed1.94.1 sources.

The same byte locations become zero, in source iteration order, with one barrier after each write. `ZeroCompatibility.erase_trace` and `upgrade_trace` relate the new history to the legacy trace shape. `trace_information` proves that the barrier's address is recoverable from the preceding write event. This is information transport for this source trace, not equality of physical observations.

No theorem here erases registers, spill slots, extra copies, freed pages or persistent storage, proves CPU/cache/timing behavior, or attests the shipped machine instructions. L1/L2/L3 and the L3 binary audit remain separate P obligations; the existing observer and simulator are unchanged. T remains exactly entropy_law, entropy_kernel, observation. The privacy target is not established.

## Finite validation and controls

`native-zeroize-pinned/`: rustc1.94.1, release opt3, assertions/overflow checks off, exact zeroize1.9.0 features alloc/default/zeroize_derive; deployed proc-macro versions/features pinned as well. Checks pass for1280 array pairs,1280 scalar cases and1024 actual consumed Zeroizing-drop pairs, including adjacent-frame bytes. These are finite byte/destructor observations. The earlier `native-zeroize/` used unicode-ident1.0.27 and is retained as auxiliary evidence only; the pinned run uses deployed1.0.24.

Six in-memory source tamper controls in `zeroize-controls.json` reject an omitted volatile write, duplicated destructor delegate, nomem barrier, nonzero byte Default, repeated iterator byte and shifted pointer cast. No dependency source was modified. These are script controls, not Kani controls. No Kani PASS, copy stub or function contract is used or re-credited.
