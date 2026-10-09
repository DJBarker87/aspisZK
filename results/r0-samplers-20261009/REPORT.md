R-B implements the R0 transcript samplers on fetched base
`01920c65827981a56ef10b7af3e3e7fdaae6fef4`, in branch
`codex/r0-transcript-rb-20261009`. The new module is
`crates/aspis-core/src/r0_transcript.rs`; the existing `transcript.rs` and
all legacy methods are unchanged. `num-bigint` and `serde_json` are
test-only dependencies. The normal dependency tree remains empty and the
library remains `no_std`.

The implementation reads byte zero as least significant, uses eight
little-endian u32 limbs, and performs 256 rounds of binary long division.
At each step the old remainder is below n and the shifted remainder is
below 2n; one subtraction suffices. Since every supported modulus is below
2^248, the intermediate fits in 256 bits. Successive divisions by P give
least-significant-first digits; each division dividend fits below 2^63.
Gamma increments the reduced integer before digit decoding, so its rank is
in [1, P^8-1]. These operations use fixed arrays and no allocation. The
modulo bias is intentional and matches the cited model.

The public API in `aspis_core::r0_transcript` is:

```rust
pub fn qm31_sample(block: &[u8; 32]) -> QM31;
pub fn ordinary_sample(block: &[u8; 32]) -> WideExact;
pub fn gamma_sample(block: &[u8; 32]) -> WideExact;
pub fn circle_sample(block: &[u8; 32], row: CircleRow) -> SecureCirclePoint;

pub enum CircleRow { First, Second }
pub enum R0Challenge {
    Qm31(QM31),
    Circle(SecureCirclePoint),
    Wide(WideExact),
    Queries([u32; 22]),
}
pub enum R0RowError {
    InvalidRow { row: u8 },
    Queries(QuerySampleError),
}
pub const QUERY_COUNT: usize = 22;
pub const QUERY_BOUND: u32 = 1 << 18;
pub const QUERY_MAX_DRAWS: usize = 64;
pub mod label {
    pub const fn R0_ROW(row: u8) -> Option<u8>;
}
```

The same module adds these inherent methods to the existing `Transcript`:

```rust
impl Transcript {
    pub fn r0_challenge_qm31(&mut self) -> QM31;
    pub fn r0_challenge_ordinary(&mut self) -> WideExact;
    pub fn r0_challenge_gamma(&mut self) -> WideExact;
    pub fn r0_challenge_circle(&mut self, row: CircleRow) -> SecureCirclePoint;
    pub fn r0_challenge_queries(&mut self) -> Result<[u32; 22], QuerySampleError>;
    pub fn r0_sample_row(
        &mut self, row: u8, canonical_message: &[u8],
    ) -> Result<R0Challenge, R0RowError>;
}
```

The primitive field and circle methods each call `squeeze_block` exactly
once, including zero, all-FF, subfield, and pole inputs. Circle output uses
the existing `secure_ood_circle_point_from_parameter` and
`circle_fallback_point`: row 25 falls back to the image of u and row 26 to
the image of 1+u. The returned QM31 coordinates embed into the model's wide
field through R-A's `WideExact::from_qm31`.

`r0_sample_row` supplies one absorb and dispatches as follows:

| Rows | Challenges | Sampler |
| --- | --- | --- |
| 0, 1, 2 | λ, χ, θ | QM31 |
| 3–12 | zc₀…₉ | QM31 |
| 13, 14 | μ, η | QM31 |
| 15–24 | semantic α₀…₉ | QM31 |
| 25, 26 | circle points | QM31 parameter, fixed row fallback |
| 27 | γ | nonzero WideExact |
| 28, 29, 30 | κ, τ, opening α₀ | ordinary WideExact |
| 31 | S | ordered q22 |

Framing is **provisional pending S1's SPEC.md**. For valid rows,
`label::R0_ROW(i) = Some(0x80 + i)` and the sole absorb hashes
`state || 0x00 || label || canonical_message`. In particular, a message-free
row passes `&[]` and still absorbs its label. The caller supplies canonical
bytes and row order; this module does not define a message schema or enforce
a complete session schedule. Invalid rows 32–255 return an error before any
hash call. Query exhaustion returns an explicit error after all eight
blocks and must cause verifier rejection.

The q22 output and state behavior match
`challenge_queries_without_replacement(22, 1 << 18, 64)`; no difference was
found. The new implementation uses a fixed `[u32; 22]` instead of a `Vec`.
Both check the stop condition before consuming the next word, not at the
end of a block. Consequently:

- A 22nd distinct value on draw 22 consumes three blocks; unused words are
  discarded and the final state is the third advance.
- Success exactly on draws 24, 32, 40, 48, or 56 consumes one extra block
  and advances once more before checking success on that block's first
  word. That word is not consumed.
- Success on draw 64 consumes eight blocks. Exhaustion also consumes eight;
  a new value at draw 65 cannot rescue failure.
- Indices are masked to 18 bits before deduplication and retain their first
  occurrence order, including when that order is descending.

The independent `generate_kats.py` uses Python integers, `%`, and `divmod`,
plus an independent schoolbook polynomial implementation for circle
coordinates. It reads no Rust outputs. `kats.json` contains 31 fixed-block
vectors for all field/circle samplers, 47 engineered query streams, and an
independent SHA-256 KAT for all 32 provisional rows. Message fixture bytes
are synthetic and do not purport to freeze S1's schema. Reproduction:

```sh
python3 results/r0-samplers-20261009/generate_kats.py --check
```

Validation passed: 9 new R0 tests, 25 existing transcript/V6 transcript
tests, and all 3 existing `r15_q22_stopping` tests. The R0 tests compare
reduction and digit reconstruction against `num_bigint::BigUint` for 2,863
blocks (all bit/carry boundaries, modulus multiples, fixed extremes, and
2,048 deterministic pseudorandom blocks). They check every possible q22
success draw from 22 through 64 against both the independent script and
the legacy implementation, including the final state and hash-call order.
They also exercise single-block consumption for every fixed KAT, both
circle poles and fallbacks, empty-message absorbs, both absorb buffer
branches, every invalid row, and 8,192 arbitrary-block row paths under
`catch_unwind`. This is test evidence, not an exhaustive machine proof of
panic freedom or a Rust-to-Lean refinement theorem.

| Check | Exit | Wall seconds | Sampled aggregate peak RSS (KiB) |
| --- | --- | --- | --- |
| Initial focused compile | 101 | 27.419 | 648048 |
| Corrected R0 release tests | 0 | 28.827 | 624576 |
| Legacy transcript release tests | 0 | 0.278 | 62864 |
| r15 q22 release tests | 0 | 14.586 | 513792 |

The initial compile failed only because a bigint test's shift amount needed
an explicit `usize` type; `focused.log` preserves that failure, and
`focused-fixed.log` records the replacement. No sampler failure was
observed. Other compiler warnings concern unchanged legacy Solana cfgs and
unused functions. Exact commands, exit statuses, source SHA-256s, and timing
are recorded in `checks.jsonl`. `run_check.py` limits builds to two jobs,
reuses one target cache, samples aggregate process-group RSS, and kills a
focused job at 6 GiB or eight minutes. These were small macOS development
checks; no heavy build or Lean replay was launched. Process swap was not
measured, and `#print axioms` is not applicable to these Rust-only checks.
No SBF performance or formal release gate is claimed.
