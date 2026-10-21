# V10 `WideExact::to_limbs` source bridge

This focused packet proves that the transparently emitted V10 `WideExact.to_limbs` body returns the same eight coordinates, in the same order, as the accepted `EbyKPushWideToQ.toLimbs` operation after a fieldwise carrier map. The equality is Lean definitional equality (`rfl`). A separate theorem proves the new extracted four-ADT carrier map agrees fieldwise with the previously accepted V10-to-EbyK carrier map.

The extraction used the frozen V10 source workspace and selected the exact inherent method path `aspis_core::field::wide_exact::_::to_limbs`, together with the four required ADTs. Charon reports the item as `Transparent`; the emitted Aeneas definition is copied byte-for-byte into `ToLimbsBody.lean`. The checker verifies that exact item and verifies the clean `Types.lean` is the emitted type file with only the `TypesExternal` import, generator option lines, and their option-description comments removed.

The Lean closure does not import generated `FunsExternal_Template` or `TypesExternal_Template`; no generated external axiom template is selected. The generated function's audit reports only `[propext, Classical.choice, Quot.sound]`. The accepted-carrier-map theorem has no axioms. Lean used the pinned 4.32 cache and `-j1 -M4400`, with zero swap.

This closes only the `to_limbs` projection correspondence. It does not establish V10/current identities for the other wide operations, establish `four_dots` caller arguments or callback state, or close the P6 / Rust `array::from_fn` boundary. The generated LLBC contains the surrounding four-dots item, but this packet makes no theorem claim about that outer method.
