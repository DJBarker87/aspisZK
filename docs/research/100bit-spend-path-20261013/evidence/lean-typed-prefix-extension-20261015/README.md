# Typed prefix extension evidence

`R1TypedPrefixExtension` proves two equalities: the result of `UnifiedSemanticRecovery.typed` and the result of `OpeningPrefixCompletion.typed` are unchanged when the trace is extended by a suffix, provided the queried address already appears in the prefix. Both proofs rewrite with `TraceAppend.tableBefore_append`.

Attempt `a` failed because the `TraceAppend` module import was missing. Attempt `b` compiled successfully. The successful run exited 0 in 1.43 s at 3,528,132 KiB peak RSS and zero swap, under 4G/6G/0 caps. Both declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.

This is a functional table-prefix equality result. It does not claim full-parser acceptance or source correspondence. Source base: `136b746805f3438507732622c9b4e50f36bf49f9`.
