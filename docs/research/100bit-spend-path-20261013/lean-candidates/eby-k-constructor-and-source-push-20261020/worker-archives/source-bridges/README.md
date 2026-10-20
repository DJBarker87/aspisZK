# EbyK checked-Q push bridge (focused proof packet)

This packet composes the source-shaped `EbyKDot.push` control proof with the copied `WideExact -> Q` conversion and the copied `checked_q`/`Q.from_limbs` body. All declarations are Lean-checked on the pinned Lean 4.32 host with the standard axioms only. It is a component packet; it does not claim the Rust caller has been adopted or that the external iterator predicate is implemented by this proof.

## Proved results

- The copied `Q.from_wide` returns the exact two Q arrays made from the eight `WideExact` limbs, in source order.
- With only `Iterator.all` exposed as a callback parameter, every successful `Q.from_limbs` result is the exact input array; every successful `checked_q` result is the four original QM31 coordinates. The copied `limbs_of`, `from_limbs`, and `checked_q` bodies pass the source-body checker in `checker/source-body-check.json` against the pinned generated `Funs.lean`.
- A successful composed push returns the two exact source Dot-call equations, each using the corresponding four WideExact limbs and the scalar's exact four QM31 limbs. It preserves `self.count < MAX_TERMS` and proves the successful checked add has numeric value `self.count.val + 1`.
- The constructor-to-push state ABI bridge is fieldwise and maps successful constructor output to the push state. The constructor and push generated types retain distinct namespaces; no replacement or merged nominal owner is claimed.

## Explicit remaining boundaries

`Dot.push` arithmetic is an explicit operation parameter. The theorem does not prove its implementation or R22 overflow behavior. `Iterator.all` is parameterized: the identity theorem works for any callback behavior, but this packet does not prove the Rust iterator's all-elements predicate semantics, nor infer canonicality from acceptance. Full Rust caller/source adoption remains open. The source adapter omits the generated `FunsExternal` template so its axiomatized callbacks are not imported.

## Reproduction and evidence

`evidence/checked-q/config.json` and `evidence/concrete-push/config.json` pin the focused targets and direct imports. Their receipts record exact source/object hashes, exit status, wall time, peak process RSS and cgroup memory, swap, and axiom reports. `evidence/state-abi/` contains the constructor-to-push bridge receipt/config. The original generated Funs body and Rust source cuts are under `rust-source/`; `checker/check-eby-k-checked-q-body.py` rechecks the exact body transformation.

The checked-Q target (module `AspisR1EbyKCheckedQAllParamV1`) passed in 1.505s with 292,425,728 bytes cgroup peak and zero swap. The composed push target (module `AspisR1EbyKPushConcreteCheckedQV1`) passed in 1.405s with 293,801,984 bytes cgroup peak and zero swap. Both print only `[propext, Classical.choice, Quot.sound]`.
