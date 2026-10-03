# R501/R504 native ABI and pointer type source inventory

Read-only source/type inventory; no build, proof check, or capture was run. This records source facts for lead review and makes no memory-semantics decision.

## Exact captures

| Capture | LLBC SHA-256 | Charon version / target metadata |
|---|---|---|
| `R501RawPartsPrecondition.llbc` | `c46d0d1fccac80c4ece4aac9cec8143b789ede55bdae39f5f6c0aa0ad6c7f1f9` | 0.1.223; `x86_64-unknown-linux-gnu`; `target_pointer_size=8`; little endian |
| `R504PointerAlignCheck.llbc` | `6265be39052b9a5897f48f9ffe5f32eb07785641255f4982e2057cdaaaefeecb` | 0.1.223; same target and pointer size |

Both captures record Aspis source revision `4f2f2f13a55425cedb2cdc19cfcf2780edbb8b35`, Charon binary SHA `b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c`, successful extraction, and no LLBC errors. Capture receipts are the adjacent `result.json`, `capture-command.json` / `launch.json`, and `SHA256SUMS.txt` files.

## Charon types and observed LLBC nodes

The pinned Charon source is commit `cb50ff16b9f1066b8a97dc06da704de2da2fa41c`; the two current source files were checked read-only on the host and match the saved copies:

- `charon/src/ast/types.rs`, SHA `144d183af79a5341424cc0ffaa99fe99a414546c05fdfccfd364e5bc2e6de5eb`.
- `charon/src/bin/charon-driver/translate/translate_types.rs`, SHA `8bc6952842edd41687cd5d7464cc1871c33e8cfcd88214ff6d7c46979c24b6cc`.
- Saved Charon OCaml generated type declarations `Generated_Types.ml`, SHA `6e977831c8fb7a3e1b6b77e1b98e5cc71de8841186f98c5de5fd68c93fdb9794`; this declares builtin `PtrFromParts of ref_kind`, `TRawPtr of ty * ref_kind`, and `TPtrMetadata of ty`.

`UIntTy` has separate variants `Usize`, `U8`, `U16`, `U32`, `U64`, `U128` (types.rs around line 805). `translate_hax_uint_ty` preserves this distinction (`Usize -> Usize`, `U64 -> U64`, translate_types.rs lines 76–84); it does not replace usize with u64 based on pointer size. Charon's `PtrMetadata` variants include `None`, `Length` (documented as usize; slice length counts elements), `VTable`, and inherited metadata (types.rs around lines 615–625). A raw pointer type is represented as `TRawPtr(ty, ref_kind)`; references as `TRef(region, ty, ref_kind)`; `TPtrMetadata(ty)` marks a metadata projection (generated Charon type source cited in the prior pointer inventory).

R501/R504 LLBC retains type expressions through `Deduplicated` IDs rather than embedding the complete type at each use. Relevant concrete operation occurrences are:

| LLBC item | Observed typed node |
|---|---|
| Fun22/Fun23 `core::slice::split_at_unchecked` | `PtrMetadata` projection from input shared slice, then `RawPtr` Shared with that metadata; `Cast::RawPtr`; `Offset` (Fun22 statement 1552, Fun23 statement 1647 in R501/R504); two `PtrFromParts Shared` calls (Fun22 1547/1575; Fun23 1642/1670), followed by shared-reference assignments. |
| Fun21 `core::slice::raw::from_raw_parts::precondition_check` | LLBC statement 1408 contains `Cast::RawPtr`; statement 1421 contains `Cast::Transmute`; statement 1461 constructs shared `RawPtr` with `PtrMetadata`, then statement 1462 has `Cast::RawPtr`. |
| Fun25 `core::num::unchecked_sub::precondition_check` | Scalar casts at statements 1697 and 1699 explicitly say `Cast::Scalar [UInt Usize, UInt U64]`. |
| Fun20 `core::slice::align_to_offsets` | Input/output signatures are referenced by deduplicated IDs; target metadata is the x86_64 record above. |

The captures' JSON stores full statement bodies, signatures, generics, spans, and metadata, but some type bodies are hash-consed/deduplicated references. These numeric IDs alone are not standalone type definitions. Charon's enum source and the exact operation tags above are the source-level type facts; no unrecorded interpretation of the deduplicated IDs is asserted here.

## Aeneas fixed-width type/rendering path

Exact current R497 Aeneas source facts and hashes:

- `src/extract/ExtractTypes.ml`, SHA `0f8ee29aa89c9456ea6c266ff8d767dcb8a83af5bbe8096d04e53582cb32c527`: `extract_literal_type` maps `TUInt int_ty` to `Std.` plus `int_name (Unsigned int_ty)` for Lean. Thus Usize and U64 keep separate generated names (`Std.Usize`, `Std.U64`).
- `src/symbolic/SymbolicToPureTypes.ml`, SHA `29f4a784b0edb1dccf895aba78ec6d5c15c081e8602f7778db264b21272c54a0`: `translate_literal_type` keeps unsigned type constructors; `TRawPtr(ty, RMut/RShared)` maps to `TAdt(TBuiltin(TRawPtr Mut/Const), generics)` (lines around 35 and 194–202). This is type translation, not address/provenance semantics.
- `Aeneas/Std/Scalar/Core.lean`, SHA `ceba1982545251f02d6e286abf23d01f4d2a691fe6934149f3a42d4a051af81e`: `UScalarTy` distinguishes Usize and U64; `UScalarTy.numBits Usize = System.Platform.numBits`, `UScalarTy.numBits U64 = 64`; `UScalar ty` stores `BitVec ty.numBits` (around lines 29–74). The cached source is `/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/aeneas-full/backends/lean/Aeneas/Std/Scalar/Core.lean`.
- `Aeneas/Std/RawPtr.lean` and `Aeneas/Std/Slice.lean` hashes are recorded in `PINNED_AENEAS_POINTER_HANDLING.md`; those are unchanged cached library sources confirmed on the same host.

The Charon target record (`target_pointer_size=8`) and Lean's `System.Platform.numBits` are separate data sources. The source inventory does not itself prove the Lean platform reduction equals 64, nor that a Rust pointer is semantically a Usize value.

## Isolated interpretation boundary

The generator's rendering path preserves `Std.Usize` globally, and its ordinary fixed-width `U64` remains separately typed. Nothing in the cited type renderer requires changing the shared `Std.Usize` definition to introduce a new local theorem/model carrier for native-ABI reasoning. Such a separate carrier could be defined in a new namespace and connected only where needed; the bridge back to generated `Std.Usize` terms would still require a proved width/conversion relation (and any pointer/address interpretation would remain a lead decision). This is a statement about the separation available in the source/type namespaces, not a claim that the bridge or pointer semantics is already proved.
