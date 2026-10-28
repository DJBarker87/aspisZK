# NBY trusted/callee cuts

Exact KMX patch SHA256 bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67.
No field-multiplication stub is introduced or reached by this lane.

| Stub | Meaning proof | Domain |
|---|---|---|
| `<[u8]>::copy_from_slice`, `<[u32]>::copy_from_slice` | KMX_CopyMeaning.loop_spec/copy_prefix | Equal lengths, valid nonoverlapping Rust slice borrows; explicit element loop from exact patch |
| `core::ptr::copy_nonoverlapping` | KMX_CopyMeaning.loop_spec/copy_frame; KMX patch differential and controls | Valid aligned disjoint typed source/destination regions for count elements |
| `<[u8]>::clone_from_slice` | KMX_CopyMeaning.loop_spec | Equal valid slice lengths |

These are the exact validated KMX replacements, not new copy implementations.
Every newly credited positive native gate must have a failing control under
this same configuration. Runtime hash reply values remain the named runtime
trust; the Port implementations check request grammar, pointers, byte lengths
and chronological call count, returning a fixed arbitrary reply. They do not
unwind SHA or prove its value. Local source/value associations remain explicit
in the bridge report; no generic framework result is counted as closure.
