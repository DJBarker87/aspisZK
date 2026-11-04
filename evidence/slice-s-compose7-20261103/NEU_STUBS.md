# Native abstraction and stub inventory

No field multiplication, field-operation stub, SHA implementation or digest
value model is used in this lane. A LPh field-stub table is therefore not
applicable. No stub_verified or function contract substitution is used.

The only kani::stub annotations are the exact KMX_copy_stubs.patch functions:
core::ptr::copy_nonoverlapping -> KMX_copy_nonoverlapping and
<[u8]>::copy_from_slice -> KMX_copy_from_slice. Domains are the source language's
valid typed live buffers, valid index/length/alignment, equal slice lengths and
required non-overlap. Frozen safe ownership/array geometry and the recorded
native memory checks establish these at the source copies. Named generic value
and outside-window laws are KMX_CopyMeaning.loop_spec/copy_frame, with
NED_WindowExtensionality.array_ext for arbitrary-index assembly. KMX patch
sha256bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67
is verified before each attempt. Each credited shape has a failing matched
control in the same configuration.

Non-scalar child abstraction uses local owned/borrowed Frame records under
ruling(y), not fabricated guards, byte transmute, writable statics, a function
pointer or Box-return stub_verified. Constructor validation replies cover every
typed format-error variant and both Result tags. Complete native field/call
association plus the existing NEM validator and NEU_BoxModel substitution bind
the SAME call. All error payloads are preserved by the child bridge and erased
uniformly by the exact source map_err in the caller.

The planned reconstruction finish oracle has only the constructors' actual
reply range: arbitrary typed success Box or InvalidInstructionData. Its use
requires both complete constructor native bridges and the named
NEU_CallDomains.transfer_reply_range/withdrawal_reply_range theorems. Without
those callees the range restriction earns no caller closure. No root extraction
or whole-root bridge is assumed. P6/D188 optionA is explicit reclassification.
