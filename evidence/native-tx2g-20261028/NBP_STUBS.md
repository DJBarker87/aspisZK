# NBP callee substitution register

No field multiplication is executed in Kani; this continuation introduces no
field-arithmetic stub. Existing NBG/LPf/LPi pairings are imported unchanged.

| Stub | Closed callee/model theorem | Domain | Caller establishment |
|---|---|---|---|
| NBP_digest_bytes, replacing atomic_statement::encode_digest_canonical | NBP_DigestEncode.result; NBP_DigestLayout.bytes; reused S2K_DigestBytes.loop_exact, DigestTotal.body_word/next_row/exhausted; native NBG_K020 | Every raw eight-u32 Digest, no canonicality requirement | Native type Digest is exactly eight M31 raw-u32 limbs; all callers pass that carrier. The unrolled stub concatenates each raw word's to_le_bytes in0..7 order. |

This is callee composition, not an arbitrary-return assumption. The stub has no
kani::assume. Runtime digest syscalls and field multiplication are not stubbed
by this register. Native/ABI/P6/compiler/source-to-ELF boundaries remain.
