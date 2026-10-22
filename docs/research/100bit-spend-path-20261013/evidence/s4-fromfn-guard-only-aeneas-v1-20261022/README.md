# Guard-only from_fn Aeneas feasibility probe

This is a single, bounded feasibility run on the exact guard-only selector LLBC, after the narrowly checked reborrow candidate transformation. It does not establish a Lean semantics theorem and did not emit Lean files.

## Inputs and transformation

- Selector LLBC: `attempts/input.llbc`, SHA-256 `7ef231eb2ade39d5eea83143f392f70aa96cc0ed253761176cd8160777530d00`. This is the v3 Guard-only Charon selection output in `evidence/s4-fromfn-guard-only-extraction-v1-20261022/attempts/02-guard-only-selector`; it is Rust 1.98 nightly input, not the frozen Solana SBF Rust 1.89 source/compiler.
- The selected function is `core::array::try_from_fn_erased`, LLBC Fun 11. Its loop has adjacent statement IDs 230/231: a temporary Local25 copies Guard ADT9 field0 (`&'Body16 mut [T]`), then a Shared reborrow reads through Local25's dereference and pointer metadata. Local25 occurs exactly three times in the body; its own type is `&'Body14 mut [T]`. Both destination/ref statements have the same source span. The strict matcher also checks fully resolved referent type equality, exact Guard field projection, Shared kind, PtrMetadata projection, and unchanged regions.
- The source-only transformer and regression test are in `attempts/transform_llbc.py` and `attempts/test_transform.py`. The matcher accepts only the exact input SHA above. The transform removes stmt230 and rewrites the two bases in stmt231, preserving all other body data and the Ref's region. Output SHA is `97ca029a1fe528f3dfe7c724e9a5793cf0a74c243917193e8db554cbf4af7772` (`attempts/output.llbc`).
- The positive exact-delta test passes. Negative tests reject a new temporary use, changed referent type, and changed source mutability. This is a candidate LLBC rewrite check, not a proof of Rust borrow semantics.

## Aeneas run

The run used the cached strict-v3 Aeneas binary SHA `8b068c351f82a3a175d9907eece9228872d1165d82ff9380873afccfc10808d9` from the build packet `evidence/s4-fromfn-strict-visitor-build-v1-20261022`. Its source pins are strict visitor `InterpMatchCtxs.v3.ml` SHA `0d2ab7873780feaea346facc38f5429144153f6e93a08aef636509505216bb18` and `InterpStatements.ml` SHA `1f1b6527bce296728cce288648e6b5f6aa4fd0f1387a06af33fee2642244b616`. Container image was pinned by digest in the raw admission record.

The run is terminal exit 2 after 0.22 seconds, peak RSS 70,400 KiB, zero swaps. Before releasing the gate, the runner verified the container process cgroup path `/system.slice/docker-dd326273cdb033f5056071b54ad07ce742e63a56e3a9f96a33238ba22564285a.scope` and actual `memory.high=1073741824`, `memory.max=2147483648`, `memory.swap.max=0`.

The first failure is type translation, before body interpretation or Lean emission: `core::ptr::metadata::metadata` at `core/src/ptr/metadata.rs:100` has a generic return type `Pointee<T>::Metadata`, represented as `BuiltinOrAuto(Pointee)`. Aeneas rejects this in `SymbolicToPureTypes.ml:111` with `Unhandled BuiltinOrAuto for trait 7; builtin_impl_data: Generated_Types.BuiltinPointee`. The run output contains no generated Lean declarations; no theorem or axioms audit is claimed. The immediate blocker is the generic Pointee associated metadata type, not MaybeUninit union lowering.

The raw runner had no post-run cgroup snapshot because Docker's transient scope disappeared after process completion; the pre-release PID/cgroup/limit evidence and in-process `/usr/bin/time -v` metrics are retained. No compiler retry was made.
