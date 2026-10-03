# Pattern schema and lowering boundary

The corrected source inventory includes the pinned imported Charon OCaml type schema and its JSON and Postcard generated decoders. They define `TPattern` and decode `NotNull` into the native type AST. The same pinned Aeneas `translate_sty` function has a case for `TRawPtr`, no case for `TPattern`, and a fallback that reports an unsupported type. Thus the observed limitation is in pure-type lowering, not evidence that the LLBC decoder failed to recognize the pattern.

The exact source copies, paths, hashes, and excerpts are in `inventory/`. This is a source-handling fact only; it does not establish a Lean representation of NonNull, pointer validity, layout equivalence, or execution correspondence.
