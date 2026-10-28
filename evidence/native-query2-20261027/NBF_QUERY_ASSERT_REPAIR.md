# Native query ghost-assertion decomposition

K014–K017 timed out. Review found aggregate `[WideExact;4]` equality in the
recording replacements (dots/values), plus array/scalar-carrier equalities.
The pinned Kani context can lower array equality through memcmp loops; K006
already exposed an unwind failure for a much smaller array equality. This is
a plausible cost source, not a demonstrated root-cause diagnosis of those
query timeouts.

K029 changes only the OWN harness's ghost equalities to explicitly unrolled
all-coordinate equalities: all4*8 words for each dots/values array, all5 inverse
words, all8 alpha/rhs/value words and all4 power words. No conjunct/coordinate,
callee domain, natural field spec or caller reply is dropped. Native query code,
including its actual selected-value equality, remains byte-identical to frozen.
The new wrapper quantifies over both gate branches. The90s harness limit and
all caps are unchanged. This is a source/shape change; none of the failed
aggregate-assertion shapes is rerun unchanged. Outcome is recorded separately.

Outcome: K029 still timed out at90s (exit1,wall102.004043041s,
peak1089752KiB,swaps0). The attempted decomposition is excluded. It does not
confirm memcmp as the cause and does not close the broader native caller.
No further query shape is rerun unchanged.
