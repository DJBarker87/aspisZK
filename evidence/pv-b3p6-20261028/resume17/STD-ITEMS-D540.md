# D540 strict std-parity items

V244 and runjoin op227 remain OPEN. Every differing/absent item is named below; no semantic-equivalence substitution is used for k-double-prime. Intrinsic and compiler-lowering items remain **V370 compiler-cohort items (owner D381/D386)**. No endpoint premise is removed, added or weakened.

Source reports: `STD-PARITY-D540.json`, `K3-STD-PARITY-D540.json`. Exact full names, monomorphisations, symbols, bodies, source lines and file hashes are in `STD-ITEM-INVENTORY-D540.json`. Previous reports are retained unchanged.

## All differing and absent source items

- `core::slice::cmp::<impl std::cmp::PartialEq for [aspis_core::field::M31]>::ne` — ABSENT DEPLOYED DECLARATION; groups transition. ordinary standard-library source item.
- `<[aspis_core::field::M31] as core::slice::cmp::SlicePartialEq<aspis_core::field::M31>>::not_equal` — ABSENT DEPLOYED DECLARATION; groups transition. ordinary standard-library source item.
- `core::ub_checks::check_language_ub` — DIFFERENT; groups K73946, K73948, external, internal, transition. ordinary standard-library source item.
- `std::ops::try_trait::NeverShortCircuit::<[u64; 4]>::wrap_mut_1::<usize, {closure@../v244/deployed_poseidon_kani16.rs:219:53: 219:61}>` — DIFFERENT; groups external. ordinary standard-library source item.
- `std::ops::try_trait::NeverShortCircuit::<[u64; 4]>::wrap_mut_1::<usize, {closure@../v244/deployed_poseidon_kani16.rs:219:53: 219:61}>::{closure#0}` — COMPILER-GENERATED / SOURCE CHANGED; groups external. V370 compiler-cohort item (owner D381/D386); closure lowering; enclosing-source comparison does not establish generated-item parity.
- `std::mem::ManuallyDrop::<std::array::Guard<'_, u64>>::new` — DIFFERENT; groups external, internal. ordinary standard-library source item.
- `<std::mem::ManuallyDrop<[aspis_core::field::QM31; 4]> as std::ops::DerefMut>::deref_mut` — DIFFERENT; groups external. ordinary standard-library source item.
- `<std::array::drain::Drain<'_, aspis_core::field::QM31> as std::iter::traits::unchecked_iterator::UncheckedIterator>::next_unchecked` — ABSENT DEPLOYED DECLARATION; groups external. ordinary standard-library source item.
- `std::array::drain::drain_array_with::<aspis_core::field::QM31, std::ops::try_trait::NeverShortCircuit<[[u32; 4]; 4]>, 4, {closure@std::array::<impl [aspis_core::field::QM31; 4]>::try_map<std::ops::try_trait::NeverShortCircuit<[u32; 4]>, {closure@std::ops::try_trait::NeverShortCircuit<[u32; 4]>::wrap_mut_1<aspis_core::field::QM31, fn(aspis_core::field::QM31) -> [u32; 4] {deployed_poseidon16::extension_limbs}>::{closure#0}}>::{closure#0}}>` — ABSENT DEPLOYED DECLARATION; groups external. ordinary standard-library source item.
- `std::ops::try_trait::NeverShortCircuit::<[u32; 4]>::wrap_mut_1::<aspis_core::field::QM31, fn(aspis_core::field::QM31) -> [u32; 4] {deployed_poseidon16::extension_limbs}>` — DIFFERENT; groups external. ordinary standard-library source item.
- `std::mem::ManuallyDrop::<u64>::new` — DIFFERENT; groups external, internal. ordinary standard-library source item.
- `std::ops::try_trait::NeverShortCircuit::<u64>::wrap_mut_1::<usize, {closure@../v244/deployed_poseidon_kani16.rs:220:30: 220:36}>::{closure#0}` — COMPILER-GENERATED / SOURCE CHANGED; groups external. V370 compiler-cohort item (owner D381/D386); closure lowering; enclosing-source comparison does not establish generated-item parity.
- `<std::array::drain::Drain<'_, aspis_core::field::QM31> as std::iter::ExactSizeIterator>::len` — ABSENT DEPLOYED DECLARATION; groups external. ordinary standard-library source item.
- `std::array::<impl [aspis_core::field::QM31; 4]>::try_map::<std::ops::try_trait::NeverShortCircuit<[u32; 4]>, {closure@std::ops::try_trait::NeverShortCircuit<[u32; 4]>::wrap_mut_1<aspis_core::field::QM31, fn(aspis_core::field::QM31) -> [u32; 4] {deployed_poseidon16::extension_limbs}>::{closure#0}}>` — DIFFERENT; groups external. ordinary standard-library source item.
- `std::ops::try_trait::NeverShortCircuit::<u64>::wrap_mut_1::<usize, {closure@../v244/deployed_poseidon_kani16.rs:220:30: 220:36}>` — DIFFERENT; groups external. ordinary standard-library source item.
- `std::mem::ManuallyDrop::<[u64; 4]>::new` — DIFFERENT; groups external. ordinary standard-library source item.
- `<std::array::drain::Drain<'_, aspis_core::field::QM31> as std::iter::Iterator>::size_hint` — ABSENT DEPLOYED DECLARATION; groups external. ordinary standard-library source item.
- `std::mem::ManuallyDrop::<std::array::Guard<'_, [u32; 4]>>::new` — DIFFERENT; groups external. ordinary standard-library source item.
- `std::mem::ManuallyDrop::<[aspis_core::field::QM31; 4]>::new` — DIFFERENT; groups external. ordinary standard-library source item.
- `std::array::<impl [aspis_core::field::QM31; 4]>::try_map::<std::ops::try_trait::NeverShortCircuit<[u32; 4]>, {closure@std::ops::try_trait::NeverShortCircuit<[u32; 4]>::wrap_mut_1<aspis_core::field::QM31, fn(aspis_core::field::QM31) -> [u32; 4] {deployed_poseidon16::extension_limbs}>::{closure#0}}>::{closure#0}` — COMPILER-GENERATED / SOURCE CHANGED; groups external. V370 compiler-cohort item (owner D381/D386); closure lowering; enclosing-source comparison does not establish generated-item parity.
- `std::ops::try_trait::NeverShortCircuit::<[u32; 4]>::wrap_mut_1::<aspis_core::field::QM31, fn(aspis_core::field::QM31) -> [u32; 4] {deployed_poseidon16::extension_limbs}>::{closure#0}` — COMPILER-GENERATED / SOURCE CHANGED; groups external. V370 compiler-cohort item (owner D381/D386); closure lowering; enclosing-source comparison does not establish generated-item parity.
- `std::mem::ManuallyDrop::<std::array::Guard<'_, [u64; 4]>>::new` — DIFFERENT; groups external. ordinary standard-library source item.
- `std::mem::ManuallyDrop::<[u32; 4]>::new` — DIFFERENT; groups external. ordinary standard-library source item.
- `<std::array::drain::Drain<'_, aspis_core::field::QM31> as std::ops::Drop>::drop` — DIFFERENT; groups external. ordinary standard-library source item.
- `std::ops::try_trait::NeverShortCircuit::<u64>::wrap_mut_1::<usize, {closure@../v244/deployed_poseidon_kani16.rs:325:69: 325:75}>` — DIFFERENT; groups internal. ordinary standard-library source item.
- `std::ops::try_trait::NeverShortCircuit::<u64>::wrap_mut_1::<usize, {closure@../v244/deployed_poseidon_kani16.rs:320:62: 320:68}>` — DIFFERENT; groups internal. ordinary standard-library source item.
- `std::ops::try_trait::NeverShortCircuit::<u64>::wrap_mut_1::<usize, {closure@../v244/deployed_poseidon_kani16.rs:319:30: 319:36}>::{closure#0}` — COMPILER-GENERATED / SOURCE CHANGED; groups internal. V370 compiler-cohort item (owner D381/D386); closure lowering; enclosing-source comparison does not establish generated-item parity.
- `std::ops::try_trait::NeverShortCircuit::<u64>::wrap_mut_1::<usize, {closure@../v244/deployed_poseidon_kani16.rs:320:62: 320:68}>::{closure#0}` — COMPILER-GENERATED / SOURCE CHANGED; groups internal. V370 compiler-cohort item (owner D381/D386); closure lowering; enclosing-source comparison does not establish generated-item parity.
- `std::ops::try_trait::NeverShortCircuit::<u64>::wrap_mut_1::<usize, {closure@../v244/deployed_poseidon_kani16.rs:319:30: 319:36}>` — DIFFERENT; groups internal. ordinary standard-library source item.
- `std::ops::try_trait::NeverShortCircuit::<u64>::wrap_mut_1::<usize, {closure@../v244/deployed_poseidon_kani16.rs:325:69: 325:75}>::{closure#0}` — COMPILER-GENERATED / SOURCE CHANGED; groups internal. V370 compiler-cohort item (owner D381/D386); closure lowering; enclosing-source comparison does not establish generated-item parity.

## Compiler-generated items without established expansion parity

- `core::panicking::panic_nounwind_fmt::runtime::panic_impl` — COMPILER-GENERATED / UNRESOLVED; groups K73946, K73948, external, internal, transition. V370 compiler-cohort item (owner D381/D386); const_eval_select macro runtime lowering; template body does not establish instantiated body parity.
- `<std::result::Result<(), u8> as std::cmp::PartialEq>::eq` — COMPILER-GENERATED / UNRESOLVED; groups transition. V370 compiler-cohort item (owner D381/D386); source body not established.
- `core::panicking::panic_nounwind_fmt::runtime` — COMPILER-GENERATED / UNRESOLVED; groups K73946, K73948, external, internal, transition. V370 compiler-cohort item (owner D381/D386); const_eval_select macro runtime lowering; template body does not establish instantiated body parity.
- `core::ub_checks::check_language_ub::runtime` — COMPILER-GENERATED / UNRESOLVED; groups K73946, K73948, external, internal, transition. V370 compiler-cohort item (owner D381/D386); const_eval_select macro runtime lowering; template body does not establish instantiated body parity.
- `core::ub_checks::maybe_is_aligned::runtime` — COMPILER-GENERATED / UNRESOLVED; groups external. V370 compiler-cohort item (owner D381/D386); const_eval_select macro runtime lowering; template body does not establish instantiated body parity.
- `std::array::try_from_trusted_iterator::next::<std::ops::try_trait::NeverShortCircuit<[u32; 4]>, std::iter::Map<std::array::drain::Drain<'_, aspis_core::field::QM31>, {closure@std::ops::try_trait::NeverShortCircuit<[u32; 4]>::wrap_mut_1<aspis_core::field::QM31, fn(aspis_core::field::QM31) -> [u32; 4] {deployed_poseidon16::extension_limbs}>::{closure#0}}>>::{closure#0}` — COMPILER-GENERATED / UNRESOLVED; groups external. V370 compiler-cohort item (owner D381/D386); closure lowering; enclosing-source comparison does not establish generated-item parity.
- `std::ptr::const_ptr::<impl *const T>::is_null::runtime` — COMPILER-GENERATED / UNRESOLVED; groups external. V370 compiler-cohort item (owner D381/D386); const_eval_select macro runtime lowering; template body does not establish instantiated body parity.
- `<fn(aspis_core::field::QM31) -> [u32; 4] {deployed_poseidon16::extension_limbs} as std::ops::FnMut<(aspis_core::field::QM31,)>>::call_mut` — COMPILER-GENERATED / UNRESOLVED; groups external. V370 compiler-cohort item (owner D381/D386); source body not established.
- `std::ptr::const_ptr::<impl *const T>::offset_from_unsigned::runtime_ptr_ge::runtime` — COMPILER-GENERATED / UNRESOLVED; groups external. V370 compiler-cohort item (owner D381/D386); const_eval_select macro runtime lowering; template body does not establish instantiated body parity.
- `<std::ops::Range<usize> as std::clone::Clone>::clone` — COMPILER-GENERATED / UNRESOLVED; groups K73946, K73948. V370 compiler-cohort item (owner D381/D386); source body not established.

## Intrinsics

Every following item has a separately compared declaration. A matching declaration is not a proof of compiler semantics. Every one remains a V370 compiler-cohort item (owner D381/D386).

- `core::intrinsics::abort` — declaration tokens IDENTICAL.
- `core::intrinsics::add_with_overflow` — declaration tokens IDENTICAL.
- `core::intrinsics::aggregate_raw_ptr` — declaration tokens IDENTICAL.
- `core::intrinsics::arith_offset` — declaration tokens IDENTICAL.
- `core::intrinsics::assert_inhabited` — declaration tokens IDENTICAL.
- `core::intrinsics::caller_location` — declaration tokens IDENTICAL.
- `core::intrinsics::const_eval_select` — declaration tokens IDENTICAL.
- `core::intrinsics::ctpop` — declaration tokens IDENTICAL.
- `core::intrinsics::cttz` — declaration tokens IDENTICAL.
- `core::intrinsics::mul_with_overflow` — declaration tokens IDENTICAL.
- `core::intrinsics::offset` — declaration tokens IDENTICAL.
- `core::intrinsics::ptr_offset_from_unsigned` — declaration tokens IDENTICAL.
- `core::intrinsics::raw_eq` — declaration tokens IDENTICAL.
- `core::intrinsics::read_via_copy` — declaration tokens IDENTICAL.
- `core::intrinsics::sub_with_overflow` — declaration tokens IDENTICAL.
- `core::intrinsics::transmute` — declaration tokens IDENTICAL.
- `core::intrinsics::transmute_unchecked` — declaration tokens IDENTICAL.
- `core::intrinsics::ub_checks` — declaration tokens IDENTICAL.
- `core::intrinsics::unchecked_add` — declaration tokens IDENTICAL.
- `core::intrinsics::unchecked_sub` — declaration tokens IDENTICAL.
- `core::intrinsics::unlikely` — declaration tokens IDENTICAL.
- `core::intrinsics::wrapping_add` — declaration tokens IDENTICAL.
- `core::intrinsics::wrapping_sub` — declaration tokens IDENTICAL.

## Consequences

`check_language_ub` is an ordinary Rust function whose operands are reversed. Its called `ub_checks` intrinsic and `const_eval_select` lowering are distinct V370 items. The ordinary source mismatch still withholds credit; it is not relabelled as an intrinsic to evade k-double-prime.

`NeverShortCircuit::wrap_mut_1` now constructs `Wrapped { f, p: PhantomData }` instead of returning a closure. The enclosing ordinary function differs; each reached old closure is also explicitly a V370 lowering item. `ManuallyDrop::new`/`deref_mut`, array `try_map` and `Drain::drop` differ. Old slice `PartialEq::ne`, `SlicePartialEq::not_equal`, and old drain iterator methods/helper are absent at those origins.

Step::forward_unchecked and TryFrom<usize> for isize now map to token-identical bodies in the same macro. The original regex skipped array-type semicolons and could not match macros or const-eligibility changes; this refinement does not alter body tokens. Derived Clone/PartialEq, FnMut call glue and const_eval_select runtime wrappers remain unestablished V370 items.

Both mask copies and reconstruct retain their prior ordinary-source parity results. Transition, external/internal linear helpers and K73946/K73948 remain WITHHELD. No further sum gate was launched after the common mismatch. Strict parity failure does not disprove the application equality; it prevents this transfer route.
