# V10 `to_limbs` installed head-slot bridge

This packet composes two checked facts: the transparent V10-emitted `WideExact.to_limbs` body equals the retained EbyK `toLimbs` implementation after the explicit V10-to-EbyK carrier map, and the concrete S4 head installer assigns that same EbyK `toLimbs` implementation to `wideToLimbs`. The theorem `literal_to_limbs_installed` states the resulting all-`Result` equality for every input; it has no canonicality or success premise.

The V10 method source/object bridge is reused from `s4-v10-to-limbs-source-bridge-v1-20261021`; the installed-head method owner is reused from `s4-current-head-term-forward-root-v1-20261021`. A namespace overlay resolves the two module trees coherently: the accepted `AspisR1FastDotsCurrent.Types` and `FunsOpsV4` owners are selected alongside the V10 transparent `ToLimbsBody` module. `receipts/namespace-overlay.json` pins every resolved overlay object and its corresponding Lean source.

The Lean theorem concerns the generated transparent method and installed model slot. It does not establish the independent Rust `core::array::from_fn` lowering boundary or the complete source-caller/runtime correspondence. It imports no V10 `FunsExternal` axiom.

Focused verification used Lean 4.32.0, `-j1 -M4400`, exit 0, 12.13 seconds, peak RSS 3,691,544,576 bytes, swap 0. The theorem's `#print axioms` result is `[propext, Classical.choice, Quot.sound]`.
