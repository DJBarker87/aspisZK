# D542 ordinary std structural arguments

Kani equivalence (P6) with std parity by token identity plus structural per-item arguments (k''').

Script-checked structural arguments; not machine proofs. All 23 ordinary instantiated items are argued. No ordinary blocker remains. V370 / D381/D386 retains intrinsics, generated glue and compiler preservation; no T field or endpoint premise changes. Historical K3 suspensions remain.

## transition

Credit RELEASED under k''' for the local Kani equivalence. Actual caller-domain and source-cone composition obligations remain.

### `core::slice::cmp::<impl std::cmp::PartialEq for [aspis_core::field::M31]>::ne`

The removed slice override delegates to removed not_equal, whose checked body is !self.equal(other). Deployed PartialEq::ne default is checked as !self.eq(other), and deployed slice eq delegates to SlicePartialEq::equal. Substitution yields the same single equal call on the same slices and negates its Boolean result once. The equal body remains token-identical in the D540 reached-item audit, including length mismatch, indexed M31 comparisons and early exit. No added reads, comparisons, panic or UB check. Derived M31 equality lowering remains V370.

Old (core/src/slice/cmp.rs:20):
```rust
{
        SlicePartialEq::not_equal(self, other)
    }
```

Deployed:
```rust
// Removed declaration: replacement path specified above; supporting bodies in JSON.
```

### `<[aspis_core::field::M31] as core::slice::cmp::SlicePartialEq<aspis_core::field::M31>>::not_equal`

This helper has no independent caller beyond slice ne in this gate. Its continuation !equal(self,other) is substituted by the checked deployed PartialEq::ne -> slice eq -> SlicePartialEq::equal path. Same lengths, element reads, early returns and negation; equal is token-identical. No new panic or UB branch.

Old (core/src/slice/cmp.rs:103):
```rust
{
        !self.equal(other)
    }
```

Deployed:
```rust
// Removed declaration: replacement path specified above; supporting bodies in JSON.
```

### `core::ub_checks::check_language_ub`

Both operands are pure, total Boolean configuration predicates: runtime !cfg!(miri), const false, and ub_checks() is the compiler UB-check flag. Swapping short-circuit order preserves the conjunction in all four Boolean cases. Neither operand reads mutable program state, panics, writes, or executes a UB precondition check. Thus every actual UB-check site retains its enable bit and its failing branch. The intrinsic flag and const_eval_select lowering remain V370, D381/D386; this argument does not discharge them.

Old (core/src/ub_checks.rs:96):
```rust
{
    // Only used for UB checks so we may const_eval_select.
    intrinsics::ub_checks()
        && const_eval_select!(
            @capture { } -> bool:
            if const {
                // Always disable UB checks.
                false
            } else {
                // Disable UB checks in Miri.
                !cfg!(miri)
            }
        )
}
```

Deployed:
```rust
{
    // Only used for UB checks so we may const_eval_select.
    const_eval_select!(
        @capture { } -> bool:
        if const {
            // Always disable UB checks.
            false
        } else {
            // Disable UB checks in Miri.
            !cfg!(miri)
        }
    ) && intrinsics::ub_checks()
}
```

Retained compiler items: `core::panicking::panic_nounwind_fmt::runtime::panic_impl`, `<std::result::Result<(), u8> as std::cmp::PartialEq>::eq`, `core::panicking::panic_nounwind_fmt::runtime`, `core::ub_checks::check_language_ub::runtime`.

## external

Credit RELEASED under k''' for the local Kani equivalence. Actual caller-domain and source-cone composition obligations remain.

### `core::ub_checks::check_language_ub`

Both operands are pure, total Boolean configuration predicates: runtime !cfg!(miri), const false, and ub_checks() is the compiler UB-check flag. Swapping short-circuit order preserves the conjunction in all four Boolean cases. Neither operand reads mutable program state, panics, writes, or executes a UB precondition check. Thus every actual UB-check site retains its enable bit and its failing branch. The intrinsic flag and const_eval_select lowering remain V370, D381/D386; this argument does not discharge them.

Old (core/src/ub_checks.rs:96):
```rust
{
    // Only used for UB checks so we may const_eval_select.
    intrinsics::ub_checks()
        && const_eval_select!(
            @capture { } -> bool:
            if const {
                // Always disable UB checks.
                false
            } else {
                // Disable UB checks in Miri.
                !cfg!(miri)
            }
        )
}
```

Deployed:
```rust
{
    // Only used for UB checks so we may const_eval_select.
    const_eval_select!(
        @capture { } -> bool:
        if const {
            // Always disable UB checks.
            false
        } else {
            // Disable UB checks in Miri.
            !cfg!(miri)
        }
    ) && intrinsics::ub_checks()
}
```

### `std::ops::try_trait::NeverShortCircuit::<[u64; 4]>::wrap_mut_1::<usize, {closure@../v244/deployed_poseidon_kani16.rs:219:53: 219:61}>`

Relate the old captured f to Wrapped.f. Construction moves the same f once and does not call it. Each call_mut invokes f once with the same argument and mutable state, then wraps exactly its result in NeverShortCircuit; the checked deployed call_mut body supplies this step. PhantomData has no runtime state or destructor. If f panics, neither side constructs the result, and f has the same remaining state; destruction drops the same f. Reached usize closures and the extension_limbs function are the exact monomorphisations recorded below. No new assertion, allocation, arithmetic, UB check or panic is introduced. Closure/FnMut lowering stays V370.

Old (core/src/ops/try_trait.rs:403):
```rust
{
        move |a| NeverShortCircuit(f(a))
    }
```

Deployed:
```rust
{
        Wrapped { f, p: PhantomData }
    }
```

### `std::mem::ManuallyDrop::<std::array::Guard<'_, u64>>::new`

MaybeDangling::new is checked to be the transparent tuple constructor MaybeDangling(value). Relate old value to new value.0, with no copies, reads, calls of T, allocation, branch or panic. Both ManuallyDrop containers suppress the same T destructor. Reached u64 and arrays contain integer field elements; reached Guard owns a live exclusive initialization-buffer borrow. None contains a dangling reference at construction or use. The alias/validity weakening of MaybeDangling has no observable effect on these live instantiations; layout preservation and drop lowering remain V370. This is not claimed for arbitrary dangling T.

Old (core/src/mem/manually_drop.rs:181):
```rust
{
        ManuallyDrop { value }
    }
```

Deployed:
```rust
{
        ManuallyDrop { value: MaybeDangling::new(value) }
    }
```

### `<std::mem::ManuallyDrop<[aspis_core::field::QM31; 4]> as std::ops::DerefMut>::deref_mut`

The checked MaybeDangling::as_mut returns &mut self.0. Under old value ~ new value.0, both yield the exclusive reference to the same live [QM31;4] storage. Its four elements have valid integer fields and no destructor. The borrow is held by the array drain; the underlying stack array remains alive and is not separately dropped. No added branch, panic, UB check, allocation or callback.

Old (core/src/mem/manually_drop.rs:280):
```rust
{
        &mut self.value
    }
```

Deployed:
```rust
{
        self.value.as_mut()
    }
```

### `<std::array::drain::Drain<'_, aspis_core::field::QM31> as std::iter::traits::unchecked_iterator::UncheckedIterator>::next_unchecked`

Removed next_unchecked maps to the checked new Drain::call_mut non-ZST arm: let p=ptr; ptr=ptr.add(1); f(p.read()). At each j<4 the old IterMut next_unchecked yields address input[j] and advances before read; new ptr does the same. Map f is invoked once afterwards. No call at j=4; same valid aligned initialized locations, same ownership transfer and panic suffix. QM31 is non-ZST with no destructor. Intrinsic pointer semantics stay V370.

Old (core/src/array/drain.rs:69):
```rust
{
        // SAFETY: `Drain` is 1:1 with the inner iterator, so if the caller promised
        // that there's an element left, the inner iterator has one too.
        let p: *const T = unsafe { self.0.next_unchecked() };
        // SAFETY: The iterator was already advanced, so we won't drop this later.
        unsafe { p.read() }
    }
```

Deployed:
```rust
// Removed declaration: replacement path specified above; supporting bodies in JSON.
```

### `std::array::drain::drain_array_with::<aspis_core::field::QM31, std::ops::try_trait::NeverShortCircuit<[[u32; 4]; 4]>, 4, {closure@std::array::<impl [aspis_core::field::QM31; 4]>::try_map<std::ops::try_trait::NeverShortCircuit<[u32; 4]>, {closure@std::ops::try_trait::NeverShortCircuit<[u32; 4]>::wrap_mut_1<aspis_core::field::QM31, fn(aspis_core::field::QM31) -> [u32; 4] {deployed_poseidon16::extension_limbs}>::{closure#0}}>::{closure#0}}>`

Removed helper is inlined into deployed try_map: old ManuallyDrop stack owner plus IterMut maps to new ManuallyDrop stack owner plus Drain::new(ptr,end,f). The only reached func is the try_map closure feeding trusted map to try_from_fn. Both owners stay live across four callbacks and suppress the original array drop. Relate remaining elements by index j as in the try_map argument, including unwind. No escaping pointer or alias; added Drain::new end pointer is one-past a live four-element non-ZST array. Removed size assertion is true (4>=4).

Old (core/src/array/drain.rs:19):
```rust
{
    let mut array = ManuallyDrop::new(array);
    // SAFETY: Now that the local won't drop it, it's ok to construct the `Drain` which will.
    let drain = Drain(array.iter_mut());
    func(drain)
}
```

Deployed:
```rust
// Removed declaration: replacement path specified above; supporting bodies in JSON.
```

### `std::ops::try_trait::NeverShortCircuit::<[u32; 4]>::wrap_mut_1::<aspis_core::field::QM31, fn(aspis_core::field::QM31) -> [u32; 4] {deployed_poseidon16::extension_limbs}>`

Relate the old captured f to Wrapped.f. Construction moves the same f once and does not call it. Each call_mut invokes f once with the same argument and mutable state, then wraps exactly its result in NeverShortCircuit; the checked deployed call_mut body supplies this step. PhantomData has no runtime state or destructor. If f panics, neither side constructs the result, and f has the same remaining state; destruction drops the same f. Reached usize closures and the extension_limbs function are the exact monomorphisations recorded below. No new assertion, allocation, arithmetic, UB check or panic is introduced. Closure/FnMut lowering stays V370.

Old (core/src/ops/try_trait.rs:403):
```rust
{
        move |a| NeverShortCircuit(f(a))
    }
```

Deployed:
```rust
{
        Wrapped { f, p: PhantomData }
    }
```

### `std::mem::ManuallyDrop::<u64>::new`

MaybeDangling::new is checked to be the transparent tuple constructor MaybeDangling(value). Relate old value to new value.0, with no copies, reads, calls of T, allocation, branch or panic. Both ManuallyDrop containers suppress the same T destructor. Reached u64 and arrays contain integer field elements; reached Guard owns a live exclusive initialization-buffer borrow. None contains a dangling reference at construction or use. The alias/validity weakening of MaybeDangling has no observable effect on these live instantiations; layout preservation and drop lowering remain V370. This is not claimed for arbitrary dangling T.

Old (core/src/mem/manually_drop.rs:181):
```rust
{
        ManuallyDrop { value }
    }
```

Deployed:
```rust
{
        ManuallyDrop { value: MaybeDangling::new(value) }
    }
```

### `<std::array::drain::Drain<'_, aspis_core::field::QM31> as std::iter::ExactSizeIterator>::len`

Only the old trusted-array preflight consumes len through size_hint: initial remaining IterMut length is 4. New try_map passes the type-level N=4 to try_from_fn, whose guard iterates exactly 4 times; no length query is exposed to a caller. At intermediate j the relation is old len=4-j and new end-ptr=4-j. The only removed size assertion is true. No changed result/panic/UB behaviour.

Old (core/src/array/drain.rs:60):
```rust
{
        self.0.len()
    }
```

Deployed:
```rust
// Removed declaration: replacement path specified above; supporting bodies in JSON.
```

### `std::array::<impl [aspis_core::field::QM31; 4]>::try_map::<std::ops::try_trait::NeverShortCircuit<[u32; 4]>, {closure@std::ops::try_trait::NeverShortCircuit<[u32; 4]>::wrap_mut_1<aspis_core::field::QM31, fn(aspis_core::field::QM31) -> [u32; 4] {deployed_poseidon16::extension_limbs}>::{closure#0}}>`

Reached T=QM31, N=4, R=NeverShortCircuit<[u32;4]>. Relate old remaining IterMut to new [ptr,end) and old initialized output prefix to the new Guard prefix. Initially both own exactly input[0..4], output empty. At step j<4 both advance the source cursor before reading input[j], invoke the same extension_limbs once, branch Continue, write output[j], advance initialized. NeverShortCircuit has no residual inhabitant. Old size_hint lower bound is exactly 4, so its removed assert!(>=4) cannot panic. Both call try_from_fn/erased with the same 4 callbacks; support bodies are checked. At exit both forget the full Guard and return the same initialized array. If a callback panics, both drop the same remaining input suffix and initialized output prefix; these are destructor-free QM31/[u32;4], so relative guard/function-drop order has no observable effect. extension_limbs is a pure field projection. Both pointer walks stay in the live array, never read end, and use the same four UB-valid accesses. ZST branch is unreachable for QM31. Pointer/layout/glue lowering remains V370.

Old (core/src/array/mod.rs:590):
```rust
{
        drain_array_with(self, |iter| try_from_trusted_iterator(iter.map(f)))
    }
```

Deployed:
```rust
{
        let mut me = ManuallyDrop::new(self);
        // SAFETY: try_from_fn calls `f` N times.
        let mut f = unsafe { drain::Drain::new(&mut me, &mut f) };
        try_from_fn(&mut f)
    }
```

### `std::ops::try_trait::NeverShortCircuit::<u64>::wrap_mut_1::<usize, {closure@../v244/deployed_poseidon_kani16.rs:220:30: 220:36}>`

Relate the old captured f to Wrapped.f. Construction moves the same f once and does not call it. Each call_mut invokes f once with the same argument and mutable state, then wraps exactly its result in NeverShortCircuit; the checked deployed call_mut body supplies this step. PhantomData has no runtime state or destructor. If f panics, neither side constructs the result, and f has the same remaining state; destruction drops the same f. Reached usize closures and the extension_limbs function are the exact monomorphisations recorded below. No new assertion, allocation, arithmetic, UB check or panic is introduced. Closure/FnMut lowering stays V370.

Old (core/src/ops/try_trait.rs:403):
```rust
{
        move |a| NeverShortCircuit(f(a))
    }
```

Deployed:
```rust
{
        Wrapped { f, p: PhantomData }
    }
```

### `std::mem::ManuallyDrop::<[u64; 4]>::new`

MaybeDangling::new is checked to be the transparent tuple constructor MaybeDangling(value). Relate old value to new value.0, with no copies, reads, calls of T, allocation, branch or panic. Both ManuallyDrop containers suppress the same T destructor. Reached u64 and arrays contain integer field elements; reached Guard owns a live exclusive initialization-buffer borrow. None contains a dangling reference at construction or use. The alias/validity weakening of MaybeDangling has no observable effect on these live instantiations; layout preservation and drop lowering remain V370. This is not claimed for arbitrary dangling T.

Old (core/src/mem/manually_drop.rs:181):
```rust
{
        ManuallyDrop { value }
    }
```

Deployed:
```rust
{
        ManuallyDrop { value: MaybeDangling::new(value) }
    }
```

### `<std::array::drain::Drain<'_, aspis_core::field::QM31> as std::iter::Iterator>::size_hint`

The sole reached size_hint consumer is try_from_trusted_iterator at initial j=0. ExactSizeIterator yields (4,Some(4)); it tests only lower>=4, which is true. Deployed try_map uses try_from_fn with fixed N=4, so erasing this true preflight and unused Some bound preserves all effects and failures. len and cursor relation are checked in the same structural family.

Old (core/src/array/drain.rs:52):
```rust
{
        let n = self.len();
        (n, Some(n))
    }
```

Deployed:
```rust
// Removed declaration: replacement path specified above; supporting bodies in JSON.
```

### `std::mem::ManuallyDrop::<std::array::Guard<'_, [u32; 4]>>::new`

MaybeDangling::new is checked to be the transparent tuple constructor MaybeDangling(value). Relate old value to new value.0, with no copies, reads, calls of T, allocation, branch or panic. Both ManuallyDrop containers suppress the same T destructor. Reached u64 and arrays contain integer field elements; reached Guard owns a live exclusive initialization-buffer borrow. None contains a dangling reference at construction or use. The alias/validity weakening of MaybeDangling has no observable effect on these live instantiations; layout preservation and drop lowering remain V370. This is not claimed for arbitrary dangling T.

Old (core/src/mem/manually_drop.rs:181):
```rust
{
        ManuallyDrop { value }
    }
```

Deployed:
```rust
{
        ManuallyDrop { value: MaybeDangling::new(value) }
    }
```

### `std::mem::ManuallyDrop::<[aspis_core::field::QM31; 4]>::new`

MaybeDangling::new is checked to be the transparent tuple constructor MaybeDangling(value). Relate old value to new value.0, with no copies, reads, calls of T, allocation, branch or panic. Both ManuallyDrop containers suppress the same T destructor. Reached u64 and arrays contain integer field elements; reached Guard owns a live exclusive initialization-buffer borrow. None contains a dangling reference at construction or use. The alias/validity weakening of MaybeDangling has no observable effect on these live instantiations; layout preservation and drop lowering remain V370. This is not claimed for arbitrary dangling T.

Old (core/src/mem/manually_drop.rs:181):
```rust
{
        ManuallyDrop { value }
    }
```

Deployed:
```rust
{
        ManuallyDrop { value: MaybeDangling::new(value) }
    }
```

### `std::mem::ManuallyDrop::<std::array::Guard<'_, [u64; 4]>>::new`

MaybeDangling::new is checked to be the transparent tuple constructor MaybeDangling(value). Relate old value to new value.0, with no copies, reads, calls of T, allocation, branch or panic. Both ManuallyDrop containers suppress the same T destructor. Reached u64 and arrays contain integer field elements; reached Guard owns a live exclusive initialization-buffer borrow. None contains a dangling reference at construction or use. The alias/validity weakening of MaybeDangling has no observable effect on these live instantiations; layout preservation and drop lowering remain V370. This is not claimed for arbitrary dangling T.

Old (core/src/mem/manually_drop.rs:181):
```rust
{
        ManuallyDrop { value }
    }
```

Deployed:
```rust
{
        ManuallyDrop { value: MaybeDangling::new(value) }
    }
```

### `std::mem::ManuallyDrop::<[u32; 4]>::new`

MaybeDangling::new is checked to be the transparent tuple constructor MaybeDangling(value). Relate old value to new value.0, with no copies, reads, calls of T, allocation, branch or panic. Both ManuallyDrop containers suppress the same T destructor. Reached u64 and arrays contain integer field elements; reached Guard owns a live exclusive initialization-buffer borrow. None contains a dangling reference at construction or use. The alias/validity weakening of MaybeDangling has no observable effect on these live instantiations; layout preservation and drop lowering remain V370. This is not claimed for arbitrary dangling T.

Old (core/src/mem/manually_drop.rs:181):
```rust
{
        ManuallyDrop { value }
    }
```

Deployed:
```rust
{
        ManuallyDrop { value: MaybeDangling::new(value) }
    }
```

### `<std::array::drain::Drain<'_, aspis_core::field::QM31> as std::ops::Drop>::drop`

Reached T=QM31 is non-ZST and has only four u32 field limbs, no Drop implementation. At every normal or panic exit, old IterMut remaining slice and new [ptr,end) denote precisely input[j..4]. Both drop that suffix once and never the moved prefix. Added offset_from_unsigned has same-allocation, ordered, aligned pointers by 0<=j<=4; empty j=4 is valid. No new failing UB check or panic. For this T all element drop glue is effect-free; output Guard drops initialized [u32;4] prefix, also effect-free. No general claim for ZST or side-effecting destructors; glue/layout semantics remain V370.

Old (core/src/array/drain.rs:35):
```rust
{
        // SAFETY: By the type invariant, we're allowed to drop all these.
        unsafe { drop_in_place(self.0.as_mut_slice()) }
    }
```

Deployed:
```rust
{
        if !T::IS_ZST {
            // SAFETY: we cant read more than N elements
            let slice = unsafe {
                from_raw_parts_mut::<[T]>(
                    self.ptr.as_ptr(),
                    // SAFETY: `start <= end`
                    self.end.offset_from_unsigned(self.ptr.as_ptr()),
                )
            };

            // SAFETY: By the type invariant, we're allowed to drop all these. (we own it, after all)
            unsafe { drop_in_place(slice) }
        }
    }
```

Retained compiler items: `core::panicking::panic_nounwind_fmt::runtime::panic_impl`, `core::panicking::panic_nounwind_fmt::runtime`, `core::ub_checks::check_language_ub::runtime`, `core::ub_checks::maybe_is_aligned::runtime`, `std::array::try_from_trusted_iterator::next::<std::ops::try_trait::NeverShortCircuit<[u32; 4]>, std::iter::Map<std::array::drain::Drain<'_, aspis_core::field::QM31>, {closure@std::ops::try_trait::NeverShortCircuit<[u32; 4]>::wrap_mut_1<aspis_core::field::QM31, fn(aspis_core::field::QM31) -> [u32; 4] {deployed_poseidon16::extension_limbs}>::{closure#0}}>>::{closure#0}`, `std::ops::try_trait::NeverShortCircuit::<[u64; 4]>::wrap_mut_1::<usize, {closure@../v244/deployed_poseidon_kani16.rs:219:53: 219:61}>::{closure#0}`, `std::ptr::const_ptr::<impl *const T>::is_null::runtime`, `<fn(aspis_core::field::QM31) -> [u32; 4] {deployed_poseidon16::extension_limbs} as std::ops::FnMut<(aspis_core::field::QM31,)>>::call_mut`, `std::ops::try_trait::NeverShortCircuit::<u64>::wrap_mut_1::<usize, {closure@../v244/deployed_poseidon_kani16.rs:220:30: 220:36}>::{closure#0}`, `std::array::<impl [aspis_core::field::QM31; 4]>::try_map::<std::ops::try_trait::NeverShortCircuit<[u32; 4]>, {closure@std::ops::try_trait::NeverShortCircuit<[u32; 4]>::wrap_mut_1<aspis_core::field::QM31, fn(aspis_core::field::QM31) -> [u32; 4] {deployed_poseidon16::extension_limbs}>::{closure#0}}>::{closure#0}`, `std::ops::try_trait::NeverShortCircuit::<[u32; 4]>::wrap_mut_1::<aspis_core::field::QM31, fn(aspis_core::field::QM31) -> [u32; 4] {deployed_poseidon16::extension_limbs}>::{closure#0}`, `std::ptr::const_ptr::<impl *const T>::offset_from_unsigned::runtime_ptr_ge::runtime`.

## internal

Credit RELEASED under k''' for the local Kani equivalence. Actual caller-domain and source-cone composition obligations remain.

### `core::ub_checks::check_language_ub`

Both operands are pure, total Boolean configuration predicates: runtime !cfg!(miri), const false, and ub_checks() is the compiler UB-check flag. Swapping short-circuit order preserves the conjunction in all four Boolean cases. Neither operand reads mutable program state, panics, writes, or executes a UB precondition check. Thus every actual UB-check site retains its enable bit and its failing branch. The intrinsic flag and const_eval_select lowering remain V370, D381/D386; this argument does not discharge them.

Old (core/src/ub_checks.rs:96):
```rust
{
    // Only used for UB checks so we may const_eval_select.
    intrinsics::ub_checks()
        && const_eval_select!(
            @capture { } -> bool:
            if const {
                // Always disable UB checks.
                false
            } else {
                // Disable UB checks in Miri.
                !cfg!(miri)
            }
        )
}
```

Deployed:
```rust
{
    // Only used for UB checks so we may const_eval_select.
    const_eval_select!(
        @capture { } -> bool:
        if const {
            // Always disable UB checks.
            false
        } else {
            // Disable UB checks in Miri.
            !cfg!(miri)
        }
    ) && intrinsics::ub_checks()
}
```

### `std::mem::ManuallyDrop::<std::array::Guard<'_, u64>>::new`

MaybeDangling::new is checked to be the transparent tuple constructor MaybeDangling(value). Relate old value to new value.0, with no copies, reads, calls of T, allocation, branch or panic. Both ManuallyDrop containers suppress the same T destructor. Reached u64 and arrays contain integer field elements; reached Guard owns a live exclusive initialization-buffer borrow. None contains a dangling reference at construction or use. The alias/validity weakening of MaybeDangling has no observable effect on these live instantiations; layout preservation and drop lowering remain V370. This is not claimed for arbitrary dangling T.

Old (core/src/mem/manually_drop.rs:181):
```rust
{
        ManuallyDrop { value }
    }
```

Deployed:
```rust
{
        ManuallyDrop { value: MaybeDangling::new(value) }
    }
```

### `std::mem::ManuallyDrop::<u64>::new`

MaybeDangling::new is checked to be the transparent tuple constructor MaybeDangling(value). Relate old value to new value.0, with no copies, reads, calls of T, allocation, branch or panic. Both ManuallyDrop containers suppress the same T destructor. Reached u64 and arrays contain integer field elements; reached Guard owns a live exclusive initialization-buffer borrow. None contains a dangling reference at construction or use. The alias/validity weakening of MaybeDangling has no observable effect on these live instantiations; layout preservation and drop lowering remain V370. This is not claimed for arbitrary dangling T.

Old (core/src/mem/manually_drop.rs:181):
```rust
{
        ManuallyDrop { value }
    }
```

Deployed:
```rust
{
        ManuallyDrop { value: MaybeDangling::new(value) }
    }
```

### `std::ops::try_trait::NeverShortCircuit::<u64>::wrap_mut_1::<usize, {closure@../v244/deployed_poseidon_kani16.rs:325:69: 325:75}>`

Relate the old captured f to Wrapped.f. Construction moves the same f once and does not call it. Each call_mut invokes f once with the same argument and mutable state, then wraps exactly its result in NeverShortCircuit; the checked deployed call_mut body supplies this step. PhantomData has no runtime state or destructor. If f panics, neither side constructs the result, and f has the same remaining state; destruction drops the same f. Reached usize closures and the extension_limbs function are the exact monomorphisations recorded below. No new assertion, allocation, arithmetic, UB check or panic is introduced. Closure/FnMut lowering stays V370.

Old (core/src/ops/try_trait.rs:403):
```rust
{
        move |a| NeverShortCircuit(f(a))
    }
```

Deployed:
```rust
{
        Wrapped { f, p: PhantomData }
    }
```

### `std::ops::try_trait::NeverShortCircuit::<u64>::wrap_mut_1::<usize, {closure@../v244/deployed_poseidon_kani16.rs:320:62: 320:68}>`

Relate the old captured f to Wrapped.f. Construction moves the same f once and does not call it. Each call_mut invokes f once with the same argument and mutable state, then wraps exactly its result in NeverShortCircuit; the checked deployed call_mut body supplies this step. PhantomData has no runtime state or destructor. If f panics, neither side constructs the result, and f has the same remaining state; destruction drops the same f. Reached usize closures and the extension_limbs function are the exact monomorphisations recorded below. No new assertion, allocation, arithmetic, UB check or panic is introduced. Closure/FnMut lowering stays V370.

Old (core/src/ops/try_trait.rs:403):
```rust
{
        move |a| NeverShortCircuit(f(a))
    }
```

Deployed:
```rust
{
        Wrapped { f, p: PhantomData }
    }
```

### `std::ops::try_trait::NeverShortCircuit::<u64>::wrap_mut_1::<usize, {closure@../v244/deployed_poseidon_kani16.rs:319:30: 319:36}>`

Relate the old captured f to Wrapped.f. Construction moves the same f once and does not call it. Each call_mut invokes f once with the same argument and mutable state, then wraps exactly its result in NeverShortCircuit; the checked deployed call_mut body supplies this step. PhantomData has no runtime state or destructor. If f panics, neither side constructs the result, and f has the same remaining state; destruction drops the same f. Reached usize closures and the extension_limbs function are the exact monomorphisations recorded below. No new assertion, allocation, arithmetic, UB check or panic is introduced. Closure/FnMut lowering stays V370.

Old (core/src/ops/try_trait.rs:403):
```rust
{
        move |a| NeverShortCircuit(f(a))
    }
```

Deployed:
```rust
{
        Wrapped { f, p: PhantomData }
    }
```

Retained compiler items: `core::panicking::panic_nounwind_fmt::runtime::panic_impl`, `core::panicking::panic_nounwind_fmt::runtime`, `core::ub_checks::check_language_ub::runtime`, `std::ops::try_trait::NeverShortCircuit::<u64>::wrap_mut_1::<usize, {closure@../v244/deployed_poseidon_kani16.rs:319:30: 319:36}>::{closure#0}`, `std::ops::try_trait::NeverShortCircuit::<u64>::wrap_mut_1::<usize, {closure@../v244/deployed_poseidon_kani16.rs:320:62: 320:68}>::{closure#0}`, `std::ops::try_trait::NeverShortCircuit::<u64>::wrap_mut_1::<usize, {closure@../v244/deployed_poseidon_kani16.rs:325:69: 325:75}>::{closure#0}`.

## K73946

Credit RELEASED under k''' for the local Kani equivalence. Actual caller-domain and source-cone composition obligations remain.

### `core::ub_checks::check_language_ub`

Both operands are pure, total Boolean configuration predicates: runtime !cfg!(miri), const false, and ub_checks() is the compiler UB-check flag. Swapping short-circuit order preserves the conjunction in all four Boolean cases. Neither operand reads mutable program state, panics, writes, or executes a UB precondition check. Thus every actual UB-check site retains its enable bit and its failing branch. The intrinsic flag and const_eval_select lowering remain V370, D381/D386; this argument does not discharge them.

Old (core/src/ub_checks.rs:96):
```rust
{
    // Only used for UB checks so we may const_eval_select.
    intrinsics::ub_checks()
        && const_eval_select!(
            @capture { } -> bool:
            if const {
                // Always disable UB checks.
                false
            } else {
                // Disable UB checks in Miri.
                !cfg!(miri)
            }
        )
}
```

Deployed:
```rust
{
    // Only used for UB checks so we may const_eval_select.
    const_eval_select!(
        @capture { } -> bool:
        if const {
            // Always disable UB checks.
            false
        } else {
            // Disable UB checks in Miri.
            !cfg!(miri)
        }
    ) && intrinsics::ub_checks()
}
```

Retained compiler items: `core::panicking::panic_nounwind_fmt::runtime::panic_impl`, `core::panicking::panic_nounwind_fmt::runtime`, `core::ub_checks::check_language_ub::runtime`, `<std::ops::Range<usize> as std::clone::Clone>::clone`.

## K73948

Credit RELEASED under k''' for the local Kani equivalence. Actual caller-domain and source-cone composition obligations remain.

### `core::ub_checks::check_language_ub`

Both operands are pure, total Boolean configuration predicates: runtime !cfg!(miri), const false, and ub_checks() is the compiler UB-check flag. Swapping short-circuit order preserves the conjunction in all four Boolean cases. Neither operand reads mutable program state, panics, writes, or executes a UB precondition check. Thus every actual UB-check site retains its enable bit and its failing branch. The intrinsic flag and const_eval_select lowering remain V370, D381/D386; this argument does not discharge them.

Old (core/src/ub_checks.rs:96):
```rust
{
    // Only used for UB checks so we may const_eval_select.
    intrinsics::ub_checks()
        && const_eval_select!(
            @capture { } -> bool:
            if const {
                // Always disable UB checks.
                false
            } else {
                // Disable UB checks in Miri.
                !cfg!(miri)
            }
        )
}
```

Deployed:
```rust
{
    // Only used for UB checks so we may const_eval_select.
    const_eval_select!(
        @capture { } -> bool:
        if const {
            // Always disable UB checks.
            false
        } else {
            // Disable UB checks in Miri.
            !cfg!(miri)
        }
    ) && intrinsics::ub_checks()
}
```

Retained compiler items: `core::panicking::panic_nounwind_fmt::runtime::panic_impl`, `core::panicking::panic_nounwind_fmt::runtime`, `core::ub_checks::check_language_ub::runtime`, `<std::ops::Range<usize> as std::clone::Clone>::clone`.

All source hashes, old/new full signatures, reached monomorphisations, supporting replacement bodies and original symbols are recorded in STD-STRUCTURAL-D542.json. Script: tools/pv-b3p6-20261028/std_structural_d542.py. No Kani/Lean/native build run in this source audit.
