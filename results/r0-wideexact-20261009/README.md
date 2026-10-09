# R-A: WideExact arithmetic

Implemented `aspis_core::field::WideExact` at source revision
`73c502add062f5267146827117b4d1cf577475ab` (base `41d8f6120`).
All nine focused release tests pass with integer overflow checks enabled;
the standalone `no_std` library check also passes. This is an arithmetic
implementation and test result, not a Rust-to-Lean refinement proof or a CU
measurement. M2 work is stopped; R-A does not change its profiles or PCS.

M1's required corrupted-byte witness was already committed separately in
`1c07e1298` (driver support: `4411a42a6`):
[rate512-q16-reject-1.json](../v8-state-only-cu-20261009/rate512-q16-reject-1.json)
and its README entry. The old `codex/v8-state-only-cu-m1` branch is deleted
locally and absent on origin. R-A is on `v8-reference`.

## Representation and decode formula for S1

**Eight canonical M31 limbs**, stored as exactly two QM31 coordinates:
`c0 + c1*v`. Put `P = 2^31 - 1`, `i² = -1`, `u² = 2+i`, `v² = u`.
For each digit `0 ≤ d_j < P`:

```text
decode4(a,b,c,d) = (a + b*i) + (c + d*i)*u
decode8(d0,...,d7)
  = decode4(d0,d1,d2,d3) + decode4(d4,d5,d6,d7)*v
  = ((d0+d1*i) + (d2+d3*i)*u)
      + ((d4+d5*i) + (d6+d7*i)*u)*v
```

Limb order is
`(c0.c0.a, c0.c0.b, c0.c1.a, c0.c1.b, c1.c0.a, c1.c0.b, c1.c1.a, c1.c1.b)`;
the basis is `(1,i,u,iu,v,iv,uv,iuv)`. This is the tuple specified by
[digitsField_apply](../../docs/research/v8-r0-close-20261007/lean/R0C/ModuloField.lean)
at lines 38–40, using
[decode4](../../docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/SamplerFieldDecode.lean)
at line 10. The generator is `u = QM31 { c0: 0, c1: 1 }`, not `2+i`.
[WideTower.lean](../../docs/research/v8-wide-reference-20261005/lean/WideTower.lean)
defines that generator at line 14, proves `qm31_wideU_not_isSquare` at line
44, defines `WideExact` at line 63, and proves `wideExact_card = P^8` at line 71.
Those Lean files were read and hashed, not modified or replayed.

The [Rust type documentation](../../crates/aspis-core/src/field/wide_exact.rs)
contains the same formula. `from_limbs([u32;8]) -> Option<WideExact>` rejects
digits ≥ P; `to_limbs()` returns the same ordered canonical digits. Byte
encoding is **32 bytes**, eight little-endian u32 limbs in that order.
`from_le_bytes(&[u8])` requires exactly 32 bytes and rejects any noncanonical
limb. This encoding is not the R-B 32-byte block-to-base-P sampler.

Coordinates are private and readable by value with `c0()` / `c1()`.
`new(c0,c1)`, `from_qm31`, and `mul_qm31` reduce raw QM31 representatives
modulo P, making the type canonical even if callers construct raw M31 values
outside the usual range. This is distinct from the strict digit/byte decoders.

## Arithmetic

All arithmetic operates in the existing QM31 tower. For `a+b*v` and `c+d*v`:

```text
product = (ac + u*bd) + (ad + bc)*v
square  = (a² + u*b²) + (2ab)*v
inverse = (a - b*v)/(a² - u*b²)
u*(A+B*u) = (2+i)*B + A*u
```

The API supplies `add`, `sub`, `neg`, `mul`, `square`, `try_inv`,
`pow(u64)`, `mul_qm31`, `from_qm31`, `is_zero`, and `ZERO`, `ONE`, `V`, `U`.
`try_inv(0)` returns `None`. For a nonzero value the QM31 norm is nonzero
because u is nonsquare; its inverse uses the existing QM31 `try_inv`.
No panicking inverse API was added. `pow` uses binary exponentiation and
defines `0^0 = 1`, matching the existing tower. No constant-time claim is made.

Only the new `field/wide_exact.rs` module and its re-export in `field.rs`
change executable Rust source. Existing M31/CM31/QM31 arithmetic is unchanged.

## Hand-computed KATs and independent checks

The product KATs use these identities, with signed coefficients reduced mod P:

| Product | Result |
| --- | --- |
| `v*v` | `u` |
| `(1+v)(1-v)` | `1-u` |
| `(u+v)(u-v)` | `2+i-u` |
| `(iv)(uv)` | `-1+2i` |
| `(1+i+u+v)^2` | `(2+3i)+(3+2i)u+(2+2i+2u)v` |

The dense product uses digits `x=[1,2,3,4,5,6,7,8]`,
`y=[8,7,6,5,4,3,2,1]`. Writing their low/high QM31 coordinates as `(a,b)`
and `(c,d)`, ordinary paper arithmetic gives:

```text
ac = (-49+99i) + (-8+70i)u
bd = (-9+91i) + (8+70i)u
ad = (-9+35i) + 30iu
bc = (-81+251i) + 174iu
ac+u*bd = (-103+247i) + (-17+161i)u
ad+bc   = (-90+286i) + 204iu
```

Expected output digits are `[P-103,247,P-17,161,P-90,286,0,204]`.
An additional inverse KAT pins `v^-1 = ((2-i)/5)*u*v`, with final two limbs
`[1717986918,1288490188]` and six preceding zero limbs.

The nine tests cover:

- All 64 basis products and 1,024 pseudorandom products against an independent
  signed-i128 schoolbook polynomial oracle using only the three tower
  relations and a final integer reduction; the oracle does not call field
  multiplication. Includes all-maximal-limb squaring.
- Ring laws and canonical outputs for 4,096 pseudorandom triples.
- Inverse round-trips on 1,024 pseudorandom values, every basis vector and
  boundary values; zero inversion returns `None`.
- QM31 embedding/mixed multiplication and powers (including exponent
  `u64::MAX`); eight P-power Frobenius applications fix sampled wide values.
- `x² != u` for 4,096 pseudorandom QM31 values and edges, plus the Euler
  identity `u^((P^4-1)/2) = -1` and `v^(P^4) = -v`. Sampling is a regression
  check, not a substitute for the Lean nonsquare proof.
- 1,024 digit/byte round-trips and boundaries, explicit coordinate and byte
  order KATs, every input length 0–65, noncanonical limbs in every position,
  and raw-QM31 constructor normalization.

## Validation and resources

Both commands ran in separate build-host scopes with **MemoryHigh=4 GiB,
MemoryMax=6 GiB, MemorySwapMax=0**. There was no simultaneous task build;
the host had about 51 GiB available and no other active build scopes when
starting. The existing pinned cache was reused; no SBF or Lean build ran.

```text
cargo test --release --config profile.release.overflow-checks=true --locked --offline -p aspis-core --lib field::wide_exact::tests -- --nocapture
cargo check --release --config profile.release.overflow-checks=true --locked --offline -p aspis-core --lib --no-default-features
```

These are command payloads for the capped scopes, not uncapped build commands.
Host: `nuc`, `dombarker@100.108.41.90`, Linux `6.8.0-142-generic`;
rustc/cargo `1.94.1`. Tests: **9 passed**, 0 failed (0.01 s test execution).
The resource recorder includes compilation and 0.5-second polling overhead.

| Job | Exit | Wall s | Sampled aggregate RSS MiB | Cgroup peak MiB | Swap bytes |
| --- | ---: | ---: | ---: | ---: | ---: |
| [WideExact tests](wide-exact-tests.json) | 0 | 25.524 | 718.84 | 685.34 | 0 |
| [no_std library check](no-std-library-check.json) | 0 | 2.502 | 517.996 | 443.078 | 0 |

[validation.json](validation.json) preserves tool versions, source-hash
verification and test/build log excerpts. [source-manifest.json](source-manifest.json)
pins 60 build-input files and the three Lean reference sources. All build-input
hashes match the build host. Full logs remain under
`/home/dombarker/project-offloads/aspis-r0-wideexact-20261009/evidence`.
The existing resource recorder's schema name is retained in the raw JSON;
the recorded commands are R-A arithmetic checks, not CU measurements.
