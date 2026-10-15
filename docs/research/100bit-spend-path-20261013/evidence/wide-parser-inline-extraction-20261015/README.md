# WideExact inline extraction attempt g

Attempt g uses the same two-QM31-half `WideExact` source (`940e31f8…d7d06`) as extraction attempt d and adds only `#[inline(always)]` before the `QM31::from_le_bytes` declaration in `field.rs` (`9b9cda68…a7f0`). The QM31 body and all four parser bodies (M31, CM31, QM31, WideExact) are byte-for-byte unchanged from attempt d. The complete source pins and attribute-only diff are retained.

Pinned Charon and Aeneas translated this input successfully using built MIR, no `--monomorphize`, and a 4G/6G/zero-swap/128-task cgroup. The output has seven nonopaque functions. `Types.lean` is byte-identical to attempt d; `Funs.lean` differs only in the QM31 source-line annotation shifted by the added attribute, and is otherwise identical after removing source-line comments. See `generated-comparison.json` for exact hashes and function names. The generated Lean was not compiled.

This bundle records an extraction experiment only; it makes no runtime adoption or source-refinement claim.
