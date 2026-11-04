# TX2:046 trait-dispatch finding

Frozen revision `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`, `crates/aspis-core/src/r0/scalar.rs` sha256 `a36f076d3333ad53e01815bda7d030ce12e9c6e30aafc475d928d4df8af11d44`.

The unresolved `WideExact::from_m31` is `<WideExact as CodeField>::from_m31`, implemented at lines 87–91; the method declaration is line 89 and its body at line 90:

```rust
impl CodeField for WideExact {
    arithmetic!(WideExact);
    fn from_m31(value: M31) -> Self {
        Self::from_qm31(<QM31 as CodeField>::from_m31(value))
    }
```

Exact callee path: `WideExact::from_qm31(<QM31 as CodeField>::from_m31(value))`. The QM31 trait method delegates to `QM31::from_cm31(<CM31 as CodeField>::from_m31(value))`; CM31 delegates to `CM31::from_m31(<M31 as CodeField>::from_m31(value))`; the base trait method canonicalizes via `M31(value.0 % P)`. This differs from the raw inherent embedding, which does not canonicalize.

Requested inventory repair: resolve TX2:046 to the trait implementation in r0/scalar.rs and include those actual call edges. Inventory left unchanged. This is a slice-boundary finding, not native proof or new CLOSED-row credit.
