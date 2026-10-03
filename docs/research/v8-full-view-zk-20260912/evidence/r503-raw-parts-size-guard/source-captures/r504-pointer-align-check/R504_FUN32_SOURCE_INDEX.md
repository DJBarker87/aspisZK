# R504 Fun32 captured alignment-predicate index

This is a structural LLBC index, not a model or correctness argument.

## Pins and declaration

- R504 LLBC: `R504PointerAlignCheck.llbc`, SHA-256
  `6265be39052b9a5897f48f9ffe5f32eb07785641255f4982e2057cdaaaefeecb`.
- R501 LLBC: `../r501-raw-parts-precondition/R501RawPartsPrecondition.llbc`,
  SHA-256 `c46d0d1fccac80c4ece4aac9cec8143b789ede55bdae39f5f6c0aa0ad6c7f1f9`.
- R504 Fun32: transparent structured
  `core::ptr::const_ptr::<impl>::is_aligned_to`, source span
  `core/src/ptr/const_ptr.rs:1372:4-1372:52`.

## R504 Fun32 body index

| LLBC statement | Source span | Exact recorded operation/route |
| --- | --- | --- |
| 1935 | `ub_checks.rs:3859:8-3861:9`, generated from `ub_checks.rs:85:19-85:42` | Calls foreign Fun40 `core::intrinsics::ctpop` with copied Local2; result goes to Local7. Its unwind route statement 1934 is `Abort UndefinedBehavior`. |
| 1971 | `const_ptr.rs:1373:12-1373:35` | `SwitchInt` on copied Local7 with `U32` literal `1`. The listed `1` case has no statements. The other branch builds panic arguments. |
| 1940, 1954 | `panic.rs` construction spans under the switch's other branch | String literal `is_aligned_to: align is not a power-of-two`. |
| 1957, 1959, 1961 | same branch | Scalar literals: signed `I32(1)` for wrapping shift and unsigned `Usize(1)` for bit-or in the recorded argument construction. |
| 1970 | `core/src/panic.rs:62:8-62:72` | `Abort Panic(core::panicking::panic_fmt)`. |
| 1976-1984 | after statement 1971 | Pointer cast/transmute operations, then `Sub Wrap` with unsigned `Usize(1)`, `BitAnd`, and `Eq` against unsigned `Usize(0)`; no further call or abort is recorded in Fun32. |

The direct function-call set is exactly `{Fun40 core::intrinsics::ctpop}`. The
error/termination set is exactly `{statement 1934 Abort UndefinedBehavior,
statement 1970 Abort Panic(panic_fmt)}`. The scalar/string constants above are
the complete literal set in Fun32's non-storage operations.

## Relation to R501 Fun21

R501 Fun21 `core::slice::raw::from_raw_parts::precondition_check` contains a
direct call at LLBC statement 1418 to R501 Fun32
`core::ptr::const_ptr::<impl>::is_aligned_to`. The call moves Local6 and
Local3 into the two arguments and stores the returned value in Local11. Its
unwind statement 1417 is `Abort UnwindTerminate`. The R501 capture and R504
capture assign the same function ID/name to this predicate; this records call
identity only.

No interpretation of pointer values, alignment, preconditions, safety, or
source behavior is asserted by this index.
