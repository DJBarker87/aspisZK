# Proposed diagnostic evidence note

R204 and R207 show that the bounded Charon extraction exposes the `Vec::extend` dispatch and concrete `SpecExtend` body. R207 additionally exposes `IntoIter::as_slice` and `Vec::append_elements`. R210 projects the LLBC to those five bodies and attempts translation; Aeneas stops in `remove_useless_joins` on an unsupported `CopyNonOverlapping` statement at `core/ptr/mod.rs:551:13–551:68` (`PrePasses.ml:2015`).

This bundle contains no Lean vector proof and adopts no external-template axiom. The first unsupported copy operation remains an obligation for a justified memory/source-semantics proof; it must not be erased or replaced by an assumed `Vec::extend_from_slice` correspondence. The projection’s opaque declarations are diagnostic markers, not proof premises.

R204’s launch record has no source revision, so none is inferred. R207 records source revision `237d48bc3f70c262a27e9a8595b9ac51d12b4e77`. The first R210 launch log records an upload assertion failure before Aeneas ran. In the later translation attempt, the child reports `TRACE_EXIT 2`; the wrapper itself exits 0 because it prints the child result without propagating it. These statuses are kept distinct in the bundle manifest.
