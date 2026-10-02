# R229 Charon `--start-from` selector repair analysis

Read-only analysis only. No extraction, build, selector retry, or source/toolchain edit was performed.

## Revisions and pinned source

The previous R226 launch used the captured campaign revision `18f8ecd7ef9731c69211a970698d1aedc872a74b`. Do not substitute the current worktree revision (`07977092976005ff691cf381d3e539d3ac06b595`) into R226 artifacts. The frozen Aspis snapshot `/home/dombarker/project-offloads/aspis-r20-r117-primal-20260930-a` lacks Git metadata.

Pinned Charon repository source is at commit `cb50ff16b9f1066b8a97dc06da704de2da2fa41c` (detached HEAD); binary SHA-256 from the R226 capture: `b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c`.

## Why the R226 brace patterns failed

The actual Rust-side `--start-from` resolver is `charon/src/bin/charon-driver/translate/resolve_path.rs`:

- Lines 100-145 special-case an impl pattern in the *first* element. Trait-impl patterns can resolve the trait, then filter its impls by a named ADT self type. An impl pattern whose final identifier is not a trait (`is_trait: false`) immediately errors as `--start-from does not support inherent impls` (lines 139-145).
- Lines 148-167 resolve subsequent path elements by enumerating each current definition's `nameable_children` and comparing the identifier. A later impl element errors with the exact first-element diagnostic at lines 165-167.

The brace syntax accepted by `charon/src/name_matcher/parser.rs` lines 104-135 makes a `PatElem::Impl`. Without `for Trait`, `{crate::circle_norm::Coeff}` is an inherent impl pattern; the `impl` word is optional in the grammar and the error display prints it. Thus moving the R226 brace pattern to the front would avoid the “first element” error but would hit the explicit unsupported-inherent-impl error. The first-element impl facility is for trait implementations, not these inherent methods.

There is a separate post-extraction name-matching rule in `charon/src/name_matcher/mod.rs` lines 110-120: patterns beginning with an impl block match against the rightmost impl in the item's full name. That generic matcher rule does not change the `--start-from` resolver's rejection of inherent impl patterns.

## Why plain Rust paths are the narrow selector

`charon/src/bin/charon-driver/hax/types/new/full_def.rs` lines 1183-1220 documents and implements `nameable_children`: for types, it includes inherent items (lines 1209-1218), collecting the type's inherent impl associated items. `resolve_path.rs` then resolves each path component in sequence. Therefore the plain type-associated Rust path `crate::...::Type::method` traverses module → type → associated method and avoids creating a `PatElem::Impl`.

The CLI docs (`docs/what_charon_translates.md` lines 45-52) define `--start-from` as repeated entry-point patterns. `translate_crate.rs` lines 965-974 resolves each one and enqueues only returned `DefId`s. This is consistent with the R226 intent to start directly at these four methods; the module/type prefixes are traversed for resolution, not used as broad start roots.

## Proposed revised four selectors

```text
crate::circle_norm::Coeff::new
crate::circle_norm::Coeff::four
crate::circle_norm::joined_inverse::line_norm::LineCoeff::new
crate::circle_norm::joined_inverse::line_norm::LineCoeff::four
```

These use no brace/impl syntax and do not introduce module-wide roots. The path to `Coeff`/`LineCoeff` narrows subsequent resolution to that type; `nameable_children` exposes its inherent methods. This is strongly supported by the implementation, but has not been validated by running extraction. Lead authorization is required before any changed extraction command is invoked.

## Exact pinned source evidence

All listed files are from the detached pinned Charon checkout at the commit above:

| File | SHA-256 | Relevant lines |
|---|---|---|
| `charon/src/bin/charon-driver/translate/resolve_path.rs` | `fe5a28d97ceacc40833a01bf4f6cdf5038f55d654c1d92b6f2d2a79ffa75d7f8` | 64-183; especially 100-145, 148-167 |
| `charon/src/name_matcher/parser.rs` | `ecdd722411bd718c1ba22773475f4ca8f2f353cc336c4671f048d8f5e733ef84` | 72-136 |
| `charon/src/name_matcher/mod.rs` | `c9ac2cb3b5c868da191f77a185868c635ff574ab3e02bd97fac95b12e7796da6` | 57-142; especially 110-120 |
| `charon/src/bin/charon-driver/hax/types/new/full_def.rs` | `83ef70b79b857297f3d5f0b4a9b112e0cb4a0b8afa29bdbc693b019327714f99` | 1183-1220 |
| `charon/src/bin/charon-driver/translate/translate_crate.rs` | `275279e88a372d7e978a0777efee1df11ae3e0cd494b3819ccdc439f6e888653` | 965-974 |
| `charon/src/options.rs` | `d68ea7c83465b3ce6ba9bea7d398c97ed03e0ff9abeee179f77ea04baabd7b04` | 91-101 |
| `charon/tests/ui/filtering/start_from.rs` | `f79423b78ce44430d0dbb3b57d21c6ce007212ca62f96311bde64538132e521f` | 1-9 |
| `charon/tests/ui/filtering/start_from_errors.out` | `a33dd68a2d8e073292f2824a1eaeaefab3a8da0ffe0c113bb5561be0f383d7d2` | 10-25 |
| `charon/tests/ui/filtering/start_from.out` | `67ad9c76efe8e1995ffff9e89a4dfd639c823e675c6281fe35623589023aa1a2` | emitted trait-impl method full name at lines 60-68 |
| `docs/what_charon_translates.md` | `b73db60c0af30b33a2e559cefe179971769d6be6d46117702002e72a567c3352` | 45-52 |

The UI test at `start_from.rs` lines 1-9 shows supported `std::slice::Iter::as_slice` and trait impl selectors, while `start_from_errors.out` lines 10-11 explicitly expects `{impl crate::Type}` to fail as an unsupported inherent impl. This is direct regression evidence for the distinction above.
