# Stage 1: preserve native physical reads

The checked FIs_Native.Calls enrichment contains the original Calls, native Aux,
and SAG_NativeFull.Shape on the same witness. FIs_Cons_Second.accepted obtains
all three from SAG_NativeFull.accepted on SourceCuts.second. No input assumption
was added. FIs_P2P_PairSelected.accepted retains this enriched witness in its
result while passing the original calls to existing consumers.

Attempts 001–005 passed on the pinned SInt2 host workspace, one capped scope
at a time. Exact source revision/hash, dependency fingerprint, target, exit,
time, RSS, swaps and printed axioms are in each receipt. Only standard axioms
occur. This is an intermediate transport stage, no top premise-removal credit.
No shipped source/artifact or other worker prefix changed.
