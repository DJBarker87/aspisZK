# R641 packed byte concatenation

Status: **GREEN, scratch only; not promoted or released.**

## Exact target

`AspisV8R19/R641PackedByteConcat.lean`, from `.r21-scratch/R641PackedByteConcat.UNVERIFIED.lean`.

`packed_bytes_concat` proves that the four source-shaped `U64` reads at offsets 0, 8, 16 and 23 (the last shifted right by 8) reconstruct the zero-extended 31-byte little-endian bit packing. The proof splits symbolic bit indices at 64, 128, 192, and 248, reuses R637 packing and out-of-range-zero facts, and R639’s byte-window identity. It does not enumerate bytes or unfold a byte-to-word recurrence.

This is serialization representation plumbing. It does not prove decoder acceptance, native execution, quotient semantics, callback chronology, privacy, or soundness.

## Attempts

- `1791109686807885000`: exit `1`, wall `0:01.39`, RSS `3738908 KiB`, swap `0`, source SHA `2569868b226bfbcecd08f5521f3e51b75ee1234363a192b25e261c6e9fc86b95`.
- `1791109705476330000`: exit `1`, wall `0:01.40`, RSS `3739156 KiB`, swap `0`, source SHA `7794270c06837f7850d003ace891156816393808c417c5c285bccaf494b9874d`.
- `1791109719641967000`: exit `1`, wall `0:01.42`, RSS `3739148 KiB`, swap `0`, source SHA `cf0bc353a98b3bdf6cd4b93d574d5241b21f993b6e245403d0dc92022259acb2`.
- `1791109735850993000`: exit `1`, wall `0:01.47`, RSS `3737888 KiB`, swap `0`, source SHA `caa1fab9be1751783ad2f23323d771651bd6c96c8196420514aed5c8e708036d`.
- `1791109742917879000`: exit `0`, wall `0:01.51`, RSS `3753472 KiB`, swap `0`, source SHA `04707f4424312b25701e1af14335b721785d1694499f62ca14eebfec8cac5580`.
- `1791109795462447000`: exit `1`, wall `0:02.02`, RSS `3754484 KiB`, swap `0`, source SHA `19a5dc81e8408e60b6f18d744a997700cbe60b7204bc63fa212631d6da3500f8`.
- `1791109825826211000`: exit `0`, wall `0:02.15`, RSS `3772896 KiB`, swap `0`, source SHA `4db9c8ad411122268932839f7fc6747b437ddf8302827c02e4d93c1c6a8fc9b8`.
- `1791109846354750000`: exit `0`, wall `0:02.12`, RSS `3773828 KiB`, swap `0`, source SHA `c522ed56b3537b66739e935cd96ea65df0cf2d46c2061c1c0a22e919350375c8`.
- `1791109864014716000`: exit `0`, wall `0:02.12`, RSS `3773916 KiB`, swap `0`, source SHA `bf36299be2b0f407c48ea5e45bf81cff737401a36a3725c8978f97e8ad1a23ef`.

Final audited green: `1791109864014716000`; exit 0, wall `0:02.12`, peak RSS `3773916 KiB`, swap `0`.

Complete `#print axioms` results for `bytePack_low`, `bytePack_high`, and `packed_bytes_concat`: `[propext, Classical.choice, Quot.sound]`.

## Manual dependency pins

- R637 scratch source SHA-256 `66e1b7c54f682324d451c5e41f066fac900e084056a3327390552b21ef11c681`; its cached OLean SHA-256 is `f0df37db98dff703f0264e72704dd5b7ef0cb9fd457c6e3658fbb167f476d3b0` at `/home/dombarker/project-offloads/aspis-r126-release-20260930-a/lib/AspisV8R19/R637PackedBitExtraction.olean`.
- R639 source SHA-256 `47c4fe099edab1a5a7f08a3de3ea4e1adcd50009fe0f7f81a31deaebccb0f580`; its cached OLean was used from the same pinned cache.

## Reproducibility pins

- Git revision: `e32255afb947ea19273553777273c56c60e3b28c`.
- Pinned source root: `/home/dombarker/project-offloads/aspis-r57-lean-src-20260929-a`.
- Cache: `/home/dombarker/project-offloads/aspis-r126-release-20260930-a/lib`.
- Lean `-j1 -M4500`; MemoryHigh 5G, MemoryMax 7G, MemorySwapMax 0, TasksMax 128.

## First remaining proposition

Connect this symbolic packed-byte reconstruction to the complete accepted decoder array and quotient composition.
