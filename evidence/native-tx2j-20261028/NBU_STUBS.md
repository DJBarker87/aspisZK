# Prescribed copy-stub register

Exact patch SHA256:
`bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67`.
No field arithmetic is stubbed and no SHA implementation is unwound.
All entries come byte-for-byte from KMX_copy_stubs.patch, never custom stubs.

| Native builtin | KMX replacement | Value theorem / domain |
|---|---|---|
| `[u8]::copy_from_slice` | KMX_copy_from_slice | KMX_CopyMeaning.loop_spec; NBU_CopyWindows.window_spec; NBU_SourceWindows.array_window/live_row; equal lengths, valid disjoint borrows and caller slice bounds |
| `ptr::copy_nonoverlapping` | KMX_copy_nonoverlapping | KMX_CopyMeaning.loop_spec/copy_prefix/copy_frame; valid nonoverlapping ranges, same element count, valid read/write ownership |
| `[u8]::clone_from_slice` | KMX_clone_from_slice | same indexed-copy laws; u8 Copy excludes Clone side effects; equal lengths |
| `Vec<u8>::extend_from_slice` | KMX_extend_from_slice | KMX_CopyMeaning.append_spec, valid allocator/capacity and successful reserve; no native credit for an unproved allocation path |
| `[u8]::to_vec` | KMX_to_vec | KMX_CopyMeaning.append_spec; valid allocator, successful allocation; no reached Vec conversion in current fixed-array cuts |
| `alloc::realloc` | KMX_realloc | KMX_CopyMeaning.realloc_prefix; valid old layout, ownership, uninitialized-byte validity, successful new allocation; no reached realloc needed by current fixed-array cuts |

The allocation qualifications are not assumed parent success. These six
annotations use one common prescribed configuration; annotations on an
unreached function do not create a parent allocation obligation. Kernel value
laws are not a pointer-provenance theorem. Native safe slice construction and
actual arrays establish the local length/range/nonoverlap domains; the existing
P6/platform/ABI/allocator trust boundaries remain unchanged. The KMX owner packet
retains its native differential and type-specific controls; this job additionally
runs member-matching positive/negative controls before crediting its cuts.

NBU_CopyWindows.rows_spec is symbolic induction over arbitrary 32-byte rows,
with frames and arbitrary prestate. NBU_SourceWindows joins emitted setSlice!
observations to those exact KMX value laws. No kernel reduction of 20 concrete
rows or whole native frontier is substituted for that induction.
