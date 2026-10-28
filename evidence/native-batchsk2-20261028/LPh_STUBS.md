# Stub and domain inventory

No field multiplication or other field-arithmetic stub is used by this lane.
No SHA implementation is unwound. The selected native callees contain no
field multiplication. The data-only NCM_Spy is the actual generic Digest32
argument, not a function-pointer observer or a `kani::stub` for a runtime syscall.
Digest values remain the existing runtime realization trust boundary.

The only `kani::stub` annotations are the exact lead-approved KMX copy
replacements below, from the unchanged KMX_copy_stubs.patch, sha256
bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67.
No new copy stub is written. Every credited shape has a matched failing
control in the same patch/configuration; see NCM_NATIVE_AUDIT.json.

| Stub | Named Lean value theorem | Domain and remaining boundary |
|---|---|---|
| core::ptr::copy_nonoverlapping -> KMX_copy_nonoverlapping | KMX_CopyMeaning.copy_prefix; loop_spec; copy_frame | T:Copy; valid aligned source/destination for count elements; nonoverlap; source reads valid; destination ownership. KMX is the adopted indexed value law, not a new pointer-validity proof. |
| [u8]::copy_from_slice -> KMX_copy_from_slice | KMX_CopyMeaning.copy_prefix; copy_frame | Equal slice lengths, valid source, exclusive destination and safe disjoint borrows; u8:Copy. |
| [u8]::clone_from_slice -> KMX_clone_from_slice | KMX_CopyMeaning.copy_prefix; copy_frame | Same equal-length u8 domain; Copy excludes custom Clone side effects. |

Window composition imports the existing pinned KMX_CopyMeaning object
b2089175f9446c5fb16e9cd145ccf1e9e4437e272d5193fb5a275d98ee4b3b0b.
NCM_KMXWindows.adjacent/disjoint/window_frame prove composition over those
value laws. Native caller/cutpoint and arbitrary full-carrier associations
remain OPEN and are never inferred from the mathematical copy law.
