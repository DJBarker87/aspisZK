# R639 packed byte-bit bridge

Status: **GREEN, scratch only; not promoted or released.**

## Target and exact boundary

`AspisV8R19/R639PackedByteBits.lean`, from `.r21-scratch/R639PackedByteBits.UNVERIFIED.lean`.

`eight_from_le_bytes_bit` proves the stated little-endian bit identity for any 31-byte packed input, source-shaped eight-byte window offset `off ≤ 23`, and `bit < 64`. It uses the existing `BitVec.fromLEBytes_getElem!` theorem and list drop/take indexing; it does not enumerate bytes or unfold the little-endian recurrence.

This is representation plumbing only. It does not prove complete 31-byte packed serialization, decoder execution, native behavior, quotient extraction, callback chronology, privacy, or soundness.

## Attempts

- `1791109385794238000`: exit `1`, wall `0:01.38`, RSS `3735332 KiB`, swap `0`, source SHA `170502dc8cb64b4b3e73bf971db63790dbd57debd8eaa88162207fb84ecd2113`.
- `1791109417148156000`: exit `1`, wall `0:01.37`, RSS `3735040 KiB`, swap `0`, source SHA `a1d03e8479ce3fda248364f8fac9e018b0d8193e4e50d2c6b55cb1f2ff548c79`.
- `1791109441118520000`: exit `0`, wall `0:01.41`, RSS `3749776 KiB`, swap `0`, source SHA `528d07169f64dd95cd6c73a2574cbc8d60576415f50b64dc71d8d8c130211cc1`.
- `1791109449569874000`: exit `0`, wall `0:01.50`, RSS `3750464 KiB`, swap `0`, source SHA `3ed08b39db10ba0d76cb16d0c83eca22f713f58985dd11cfad36fed08c8502a5`.
- `1791109463266238000`: exit `1`, wall `0:01.67`, RSS `3735080 KiB`, swap `0`, source SHA `7d6bb8c7d603aa54ff4da76e169cfb5e336a9b85594ca94dd35231e9fc153df4`.
- `1791109490292862000`: exit `1`, wall `0:01.47`, RSS `3736052 KiB`, swap `0`, source SHA `9154f091142772fced9be6afd05720818e3f5d654761da1997ecd246c79090d7`.
- `1791109504153031000`: exit `1`, wall `0:01.64`, RSS `3736080 KiB`, swap `0`, source SHA `c4fc9225b86ce81d61df5ec494d9e9ed06367bca35c4cd7c15125644b2e62a9c`.
- `1791109513635064000`: exit `1`, wall `0:01.63`, RSS `3737252 KiB`, swap `0`, source SHA `d26d92fe56e7b30eedacbba1e36b86a253d5ec2846922f3b6e7664612a820c48`.
- `1791109530982422000`: exit `0`, wall `0:01.75`, RSS `3752276 KiB`, swap `0`, source SHA `f8dcec26104395114ef371ba435bd61568a2902f3a8bf98ebdca3c873139768a`.
- `1791109540317412000`: exit `0`, wall `0:01.74`, RSS `3752288 KiB`, swap `0`, source SHA `47c4fe099edab1a5a7f08a3de3ea4e1adcd50009fe0f7f81a31deaebccb0f580`.

Final green: `1791109540317412000`. Complete `#print axioms`: `[propext, Classical.choice, Quot.sound]`.

## Pins

- Git revision: `e32255afb947ea19273553777273c56c60e3b28c`.
- Source root: `/home/dombarker/project-offloads/aspis-r57-lean-src-20260929-a`.
- Cache: `/home/dombarker/project-offloads/aspis-r126-release-20260930-a/lib`.
- Lean: `-j1 -M4500`, MemoryHigh 5G, MemoryMax 7G, MemorySwapMax 0, TasksMax 128.

## Next boundary

Concatenate this word bit identity with the existing symbolic 31-byte word layout; that remains separate from accepted decoder and quotient composition.
