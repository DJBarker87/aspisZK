# R298 R294 `core::slice::last` closure inventory

This read-only inventory decodes hash-consed types and follows the typed-reference behavior recorded in the pinned R274 Charon `DepsForItem` source. It does not edit declaration rows, translate LLBC, or establish source semantics.

R294 Fun12 is `core::slice::<impl>::last`, external (`is_local=false`) and Transparent, with a Structured body. The function metadata span is file id 14, `core/src/slice/mod.rs:281:4–281:42`; its body span is lines 282–283. The decoded signature takes a shared reference to `[T]` under one bound region and type variable and returns `core::option::Option<&T>` (Type9). Decoded signatures and body are saved as JSON files.

The complete pinned typed dependency closure contains only Fun12 and Type9 (`core::option::Option`), with one edge, Fun12 → Type9. It reaches no function declaration, trait declaration, trait implementation, or global; specifically it does not reach an `Iterator::try_fold` declaration. R294's full `ordered_decls` has 161 entries; Type9 is at index 6 and Fun12 at index 121, so the direct dependency precedes the root there. The closure has no missing references, unknown typed-reference shapes, or cycles under the mirrored rules.

R294 LLBC SHA-256 is `bf5ea0b6f68ab17ef73d3e721c70c9193a0682d95dcbcaf693e93187cf71da6f`; pinned R274 reorder source SHA-256 is `8a1176e29a51a83c82ff5a7df2aa11021e3e0c254e9fd6c656c0a92314ba2632`. `inventory.json` records the extraction's verified project source hashes and source revision. R294 records `contents: null` for file id 14, so the standard-library `slice/mod.rs` bytes are not present in the artifact and have no standalone source-file hash here.

This only inventories declaration metadata and the root's generic signature. It does not choose a representation or premises for a future theorem, and makes no claim that the body faithfully implements a mathematical `last` operation.
