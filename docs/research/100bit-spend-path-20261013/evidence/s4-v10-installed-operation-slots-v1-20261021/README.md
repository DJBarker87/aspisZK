# V10 installed operation-slot maps

This packet proves all-Result equations from the literal typed V10 helper adapters to the explicit operations installed by `S4ConcreteTailInstallRootV1.install`:

- `literal_from_limbs_installed` maps the V10 typed `wideFromLimbs` slot through the installed checked EbyKFinish `WideExact.from_limbs` body and its fieldwise result map.
- `literal_add_installed` maps the V10 typed `wideAdd` slot through the installed `currentWideAddS4` operation.
- `current_add_body` exposes that adapter as the transparent generated `AspisR1CurrentWide.WideExact.add` body.

The operation source map records that V10, EbyKFinish, and CurrentWide all pin the same `crates/aspis-core/src/field/wide_exact.rs` bytes (`6260fa9d…`). V10's raw `FunsExternal_Template` declares `add` and `from_limbs` as axioms. This packet does not import those axioms or assert a Lean equality to them; it proves the named typed source-cut slots equal the explicit checked implementations selected by the concrete installer, with same-source-file identity checked separately.

Validation: Lean 4.32.0, `-j1 -M4400`, exit 0, 6.21 s, peak process RSS 3,698,573,312 bytes, swap 0. All theorem audits return `[propext, Classical.choice, Quot.sound]`. `check_packet.py` validates packet hashes, direct import pins, exact source hashes for all three extraction input inventories, the V10 translation entries and transparent implementation bodies. No `.olean` is packaged. Rust `from_fn`/P6 and raw external linkage remain separate boundaries; production sources are unchanged.
