# Guard-body from_fn Aeneas feasibility probe

This records one bounded Aeneas run on the changed, minimal Guard-only LLBC selector. It is a feasibility diagnostic, not a Lean theorem or a frozen SBF-source result. The LLBC came from the retained Rust 1.98 nightly selector workspace, not the frozen Solana SBF Rust 1.89 compiler/source.

## Pinned selector and checked candidate transform

- Exact selected LLBC: `attempts/selected-input.llbc`, SHA-256 `170490594c9ee2b994fd59b33062f439c2d1f90f2c12241b8e1a71d57b4eb8a4` (49 functions, 17 types, no Charon errors). This is the narrower cut without transparent slice-index or slice-length bodies. `Pointee` and `core::ptr::metadata::metadata` are absent. `Guard`, `push_unchecked`, and Guard drop are transparent; `MaybeUninit` is opaque; slice length and `get_unchecked_mut` remain foreign.
- `attempts/input.llbc` is the exact matcher input above. The narrow transform source and exact input/output hashes are retained in `attempts/transform_llbc.py` and `attempts/transform-receipt.json`.
- It matches exactly one adjacent pair in `try_from_fn_erased` Fun 11: statement IDs 230/231 and temporary Local25. The source is the copy of Guard ADT9 `array_mut` field0 as `&'Body16 mut [T]`; Local25 has type `&'Body14 mut [T]`; the next statement creates a Shared reborrow through Local25 and copies its PtrMetadata. The temporary occurs exactly three times in the body, and the source statement spans match. The matcher compares fully resolved referent types and leaves the borrow regions unchanged.
- Candidate output: `attempts/output.llbc`, SHA-256 `47921fa66c7649fb7da70ed9450429ee2b48f709905ed72af63965203622b876`. Positive exact-delta and negative extra-use, changed-referent-type, and changed-mutability tests pass. This checker validates only the LLBC rewrite shape; it is not a proof that the Rust semantics are preserved.

## Aeneas result

The cached strict-v3 Aeneas binary SHA was `8b068c351f82a3a175d9907eece9228872d1165d82ff9380873afccfc10808d9`; its build/source pins and resource-capped build receipt are in `evidence/s4-fromfn-strict-visitor-build-v1-20261022`.

The run is terminal exit 2 after 0.33 seconds, peak RSS 79,024 KiB, zero swaps. Before releasing the gate, the runner verified host PID 1183455 in `/system.slice/docker-d8c86e84eec84acf18170c01ce0b39b23d7c2181cf62096c4acefab2fb308e56.scope`, with actual `memory.high=1073741824`, `memory.max=2147483648`, and `memory.swap.max=0`.

Aeneas passed the earlier `BuiltinOrAuto(Pointee)` type-translation failure after removing the slice-index and slice-length selectors. It then failed to match loop contexts at `InterpJoin.ml:2209`, source `core::array::try_from_fn_erased`, lines 912–921. The source context retains Guard `array_mut=MB@11(slice)` plus a loop abstraction carrying `MB@1` and `ML@11`; the projected target has Guard `array_mut=⊥` and `buffer -> MB@0(slice)`. Thus exposing transparent Guard/push/drop while leaving `MaybeUninit` opaque did not make the loop fixedpoint join succeed. No Lean output was emitted and no axioms audit is claimed.

The raw run directory retains the admitted limits and process metrics. Docker's transient cgroup was removed after exit, so no post-run cgroup counter snapshot is claimed. The first, broader selector's `BuiltinPointee` failure is separately recorded in `evidence/s4-fromfn-guard-only-aeneas-v1-20261022`; this second run is a changed selector/input, not an unchanged retry.
