# NPE_ ShrAmt bridge check (2026-11-10)

Target not yet established. This job changes no ledger row, trust row, RSL, security contract or shipped source. It checks one hand model, the ShrAmt encoding bridge recorded in `evidence/prov-p1h-20261109/PCQH_HAND_MODELS.json` (PCQH-C2, failure F1), against Rust's semantics and against the pinned Charon/Aeneas translation. Frozen source 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387; worktree head 49f906b18f6. Five of the six budgeted host scopes were used, each capped at 3G/4G with swap 0, tasks 64 and a 300 s timeout; none was raised. The receipts are in `NPE_RECEIPTS.jsonl`.

## The bridge and where it is used

The bridge text is in `inputs/PCQH_shr_prelude.lean`; the same text is pasted into the two equality files. It defines a class `ShrAmt α` with `toU32`, gives it two instances, `I32 ↦ IScalar.hcast .U32` and `Usize ↦ UScalar.cast .U32`, and defines a fresh-namespace `Std.Usize.wrapping_shr x y := Aeneas.Std.Usize.wrapping_shr x (toU32 y)` (and `wrapping_shl` the same way). Only these two amount types have instances, so an emitted shift with any other amount type fails to elaborate. It cannot be reinterpreted silently.

There are three sites:

| file | definition | Rust | amount | status |
|---|---|---|---|---|
| PRVEq_NFN_ExtractedGeometry_h1.lean:603 | fast_domain.fibre_point | `TABLE_B[index >> 9]` (fast_domain.rs:286) | literal `9`, type i32 (Rust's default for an unsuffixed shift RHS) | credited, PCQH_L008 exit 0 |
| PRVEq_RPz7_FIo_NativeFuns_h2.lean:65 | transport row_loop.body | `j >> i` | usize | not credited (the file did not compile clean; F4) |
| PRVEq_RPz7_FIo_NativeFuns_h2.lean:69 | transport row_loop.body | `i2 << i4` | usize | not credited (F4) |

The bridge only replaces `wrapping_shr`/`wrapping_shl`, so it is used only in the overflow-checks OFF configuration. No checked-configuration gate site goes through it.

## (1) Rust semantics

The Rust Reference, *Expressions → Operator expressions → Overflow*, rule `[expr.operator.int-overflow.shift]`, says that using `<<` or `>>` "where the right-hand argument is greater than or equal to the number of bits in the type of the left-hand argument, or is negative" is overflow. Rule `[expr.operator.int-overflow.intro]` says overflow panics in debug builds and that `-C overflow-checks` controls this. *Behavior not considered unsafe → Integer overflow* says builds without checks may wrap silently, using two's-complement conventions (RFC 560). The Reference does not spell out the exact wrapped value of a shift. The rule is RFC 560's and rustc's MIR `BinOp::Shr`/`Shl` semantics: the shift uses only the low log2(BITS) bits of the two's-complement right operand, so the amount is `y mod BITS`, Euclidean. `core::ops::Shr` is implemented for every left/right pair of integer types (core/src/ops/bit.rs `shr_impl_all`, nightly-2026-09-17), so the right operand keeps its own type.

The MIR that rustc emits (NPE_S1, `--emit=mir`, nightly-2026-09-17 and 1.94.1) shows this directly. With checks on, an i32 amount produces `_9 = copy _8 as u32 (IntToInt); _10 = Lt(move _9, const 64_u32); assert(move _10, "attempt to shift right by ...")` followed by `Shr(move _7, move _8)`, where the original i32 is the operand. A usize amount produces `Lt(copy _8, const 64_usize)` on the full usize, with no truncation. With checks off, only `Shr(move _7, move _8)` remains. So the checked condition is "amount reinterpreted as the unsigned type *of its own width* < BITS".

I ran the test on the host (`NPE_shift_test.rs`, NPE_S1, exit 0) with x = 0xdeadbeef12345678 : usize on a 64-bit target. Both toolchains were used, with overflow-checks on and off at opt-level 0 and 3. All 4 binaries of each configuration print identical output (`NPE_S1/stdout.log`).

| amount y | checks ON | checks OFF `>>` | model: as u32, then mod 64 |
|---|---|---|---|
| 9i32 | ok 0x6f56df77891a2b | 0x6f56df77891a2b | 9 → same |
| -1i32 | PANIC | 0x1 | 4294967295 → 63 → 0x1 |
| 40i32 | ok 0xdeadbe | 0xdeadbe | 40 → same |
| 64i32 / 65i32 | PANIC | x / x>>1 | same |
| -55i32 | PANIC | 0x6f56df77891a2b (= >>9) | 4294967241 → 9 → same |
| i32::MIN | PANIC | x | 2147483648 → 0 → same |
| 9usize / 40usize | ok | same as i32 | same |
| 64usize, usize::MAX | PANIC | x, 0x1 | same |
| 2^32+3 usize | **PANIC** | 0x1bd5b7dde2468acf (= >>3) | as u32 = 3 → same OFF |
| u32 by 40i32 | PANIC | 0xdeadbe (mask 5 bits) | same |

The `<<` rows agree the same way. With checks OFF, the model matches Rust on every case.

## (2) Translation

The LLBC is the one from the existing `PCQH_E001` extraction: frozen 4bb3b3f, `--mir built`, release, no overflow flags, charon 0.1.223, target x86_64 with 8-byte pointers. Its sha256 060de079… equals the pin in `PCQH_E001_PINS.json`. It was reused, not re-extracted. The `fibre_point` shift node is (NPE_S2, `NPE_S2/NPE_llbc_aspis_r1_cost_probe__fast_domain__fibre_point.json`):

```
BinaryOp [{"Shr": "Wrap"}, Move(local 13 : usize), Const(Signed I32 "9" : I32)]
```

Both operands keep their original Rust types. There is no cast of the amount to u32, the overflow mode is `Wrap`, and the body has no `Assert`. Aeneas b59d5188-extended emits this node as `Std.Usize.wrapping_shr index 9#i32`, which is the F1 elaboration failure. The row_loop sites are not in this LLBC. Their emission (PCQ_E410, reused by PCQH) passes a `Usize` amount in the same way.

The pinned Aeneas Std is the one the gate uses: LEAN_PATH of PCQH_L008, Aeneas oleans in `codex-cx-ledger8-cache-20261104/NNI_20261111/NNG119_seed`, printed in NPE_S3:

- `Usize.wrapping_shr : Usize → U32 → Usize := UScalar.wrapping_shr`, and `UScalar.wrapping_shr x s = x.bv.ushiftRight (s.val % ty.numBits)`. The amount must be U32, and the function masks with no check. `wrapping_shl` is the same with `shiftLeft`.
- `IScalar.hcast tgt x = BitVec.signExtend tgt.numBits x.bv`. From I32 to U32 this is the identity on the 32 bits, which is Rust's `as u32`. `UScalar.cast tgt x = BitVec.zeroExtend tgt.numBits x.bv`; from Usize to U32 this truncates mod 2^32, which is Rust's `as u32`.
- Checked `>>>`: `UScalar.shiftRight x s := if s < numBits then ok … else fail integerOverflow`. Both `shiftRight_UScalar` (any unsigned amount type, full value) and `shiftRight_IScalar` (`if s ≥ 0 then shiftRight s.toNat else fail`) exist as HShiftRight instances, for Usize/U32 and for I32 amounts. `<<<` is the same.
- `UScalarTy.numBits .Usize = System.Platform.numBits`, which the library leaves abstract as 32 or 64.

## (3) Verdict

### OFF configuration (where the bridge is used): faithful for all amounts

`NPE_ShrAmt.lean` was compiled in NPE_S5 with exit 0. Its `#print axioms` lists propext and Quot.sound only, plus Classical.choice for one lemma; there is no sorry. The file states Rust's wrapping shift as `rustShr x y := ⟨x.bv.ushiftRight (Int.toNat (y % W))⟩`, with W = `UScalarTy.numBits .Usize` and y the amount's mathematical value, and `rustShl` the same way. It then proves, for all x and all y:

- `bridge_shr_i32` / `bridge_shl_i32`: `Usize.wrapping_shr x (IScalar.hcast .U32 y) = rustShr x y.val` for y : I32, negative values included.
- `bridge_shr_usize` / `bridge_shl_usize`: the same for y : Usize, with `UScalar.cast .U32`.

The reason is that `as u32` keeps the low 32 bits of the two's-complement amount, and W (32 or 64) divides 2^32. So `(y mod 2^32) mod W = y mod W`, which is exactly Rust's low-log2(W)-bit mask. For a negative i32, `as u32` gives 2^32 + y, and mod W this has the same low bits as y. The lemmas hold for both values of `System.Platform.numBits`, so the bridge adds no width assumption.

The remaining condition is not specific to the bridge. Rust masks by the target's BITS (64 on the x86_64 extraction target and on SBF), and the library masks by `System.Platform.numBits`. The two agree when Lean's Usize width equals the target width. That is the library-wide Usize model shared by every gate module, not something the bridge introduces. For the credited fibre_point site the amount is the constant 9, so even this condition does not matter: both widths give `index >> 9`. `hcast .U32 9#i32 = 9#u32` holds by `rfl`, which is also what the gate text `wrapping_shr index 9#u32` uses.

### Checked configuration: the bridge is not used

No gate site in checked mode goes through ShrAmt, because ShrAmt only wraps `wrapping_*`. I still checked whether the claim would hold if "as u32, then the library's checked U32 shift" were used:

- **i32 amounts: faithful for all amounts.** rustc's assertion is literally `(y as u32) < BITS`, and the model fails exactly when it fails. Every negative i32 maps to at least 2^31, which is at least BITS, so the model fails where Rust panics. `checked_i32_via_u32` unfolds the U32 check. `checked_i32_direct_iff` proves that the library's direct I32 shift has the same failure set: `(y ≥ 0 ∧ y < W) ↔ (hcast .U32 y).val < W`.
- **usize (and any wider than 32-bit) amounts: NOT faithful.** rustc checks the full usize value against 64, but `as u32` truncates. The counterexample is y = 2^32 + 3: Rust panics (NPE_S1), while the model gives `x >> 3`. The construction is faithful only on the domain y < 2^32. The faithful checked translation is the library's own heterogeneous `>>>` (`shiftRight_UScalar`/`shiftRight_IScalar`), which needs no bridge.

So the bridge must not be reused for checked shifts with usize amounts. In checked mode, the domain in which "as u32 then checked U32 shift" is faithful is: every i32 amount, and usize amounts below 2^32. No gate site is in checked mode through the bridge, so no site is affected. Separately, F4 (the gate's row_loop.body uses checked `>>>` while the OFF emission masks) is a gate-model difference that this check does not touch. The reachable row_loop amounts (at most 8, per PCQH-C5) are inside every domain above.

## Trust-inventory text

The bridge is faithful on all inputs in the configuration where it is used: OFF, with I32 and Usize amounts. The removal condition is:

> ShrAmt bridge: verified against Rust semantics and the pinned translation, NPE_ 2026-11-10

To be read with this scope: it covers the overflow-checks OFF configuration only (lemmas `NPE.bridge_sh{r,l}_{i32,usize}` in `evidence/shramt-20261110/NPE_ShrAmt.lean`). The bridge must not be reused for checked shifts with amounts wider than 32 bits. Lean's Usize width equalling the target width remains the library-wide assumption.

## What this does not establish

- The Lean statement of Rust's semantics (`rustShr`/`rustShl`) is a hand-written formalisation of the Reference, RFC 560 and the MIR rule. It is checked against rustc's MIR and against compiled binaries on x86_64 (two toolchains, O0 and O3), not on SBF. The deployed SBF build configuration (R22) is not analysed.
- The NPE_ lemmas are not yet imported into PRVEq_NFN_ExtractedGeometry_h1. That would turn the hand model into a proved bridge inside the credited file and is the next deliverable. The row_loop family stays OPEN (F4).

Target not yet established.
