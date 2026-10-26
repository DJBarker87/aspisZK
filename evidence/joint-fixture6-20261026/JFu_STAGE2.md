# Stage 2: forward scalar decoder and real public windows

JFu_DigestDecode.success proves forward emitted eight-word digest decoding on
canonical32-byte arrays, using eight symbolic bounded scalar-word lemmas.
JFu_DigestSlice.success transports this into the actual cast/unwrap/decode call.
No whole1880-byte decoder reduction or loop unfolding is used.

JFu_generate_public.py deterministically selects47 actual public digest windows:
anchor, snapshot root/frontier, afterstate root/frontier, and payment digests.
Each generated module proves length, exact selection from retained publicInput,
canonicality one four-byte word at a time, and successful emitted read_digest.
The generator preflight --check passes. No exceptional huge recurrence cells
exist: each check is at most one fixed32-bit word or one32-byte bounded window.
The first module JFu_PublicDigest00 passed before the remaining serial batch.
Those later modules remain unvalidated until their individual receipts succeed.

Executable source decoder/serializer diagnostics are retained separately:
1455 semantic bytes, not physical1880 bytes. JFu_SEED_DIAGNOSTIC.json computes
SHA256 on domain || zero || le32(1455) || semantic || actual proof c1_root.
This diagnostic has no kernel correspondence certificate yet.
No premise removed, no full native acceptance or full fixture claimed.
