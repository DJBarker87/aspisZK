# Native stubs

No field multiplication stub is introduced. No SHA/hash implementation is
unwound. No open lower verifier unit is stubbed to a successful result.

The exact KMX_copy_stubs.patch is applied only in the private scratch tree:
sha256 bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67.
Native harnesses that construct or transport Pubkeys use the patch's
KMX_copy_nonoverlapping. Snapshot's one-byte success also uses its KMX_to_vec.
Each gate has a separately named wrong-result/identity control with the same
stub attributes. A positive gate has no native credit until its own control
fails for an asserted semantic property. TIMEOUT/codegen/translation errors
are not passing controls. Per-attempt frozen graph and unchanged lock checks
run inside the admitted scope before/after each Kani invocation.

The wrappers call the actual SDK borrow implementations on the small typed
AccountInfo values constructed in the harness; this is local evidence within
that class. It neither replaces nor enlarges S2TrustedSdkBorrow, runtime/ABI,
allocator, source/ELF, or arbitrary-account admissibility boundaries.
