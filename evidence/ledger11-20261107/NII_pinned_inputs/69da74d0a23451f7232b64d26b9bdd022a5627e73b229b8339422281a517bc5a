# Scalar word bound isolation

K041 executes only ONE source word body (no query_words/IntoIter reconstruction)
but inherited unwind90 from the compound byte-buffer harness. K042 uses24:
the caller's active array has22 u32 cells; the u32 contains backend has at most
one16-lane chunk, a16-lane fold and a remainder shorter than16. The scalar
body has no source loop. The framework must still check unwinding assertions;
any reached copy requiring a larger bound is a failure, never a pass. The
prescribed KMX patch is unchanged. Timeout and memory caps are unchanged.
This is a smaller generated verification graph, not a larger-budget retry.
Native metadata shows ChunksExact/fold/any; SBF macro source is separately
retained without inferring Kani source identity from those names alone.
