# Bounded arithmetic prerequisite review

The three unchanged SentinelPermutation files and the RootModelCell files use
explicit literal states of type `Fin 16 → Scalar`, with a separately named
state and theorem for each individual round. A predecessor state is a literal
vector, not a definition recursively evaluating all preceding rounds. The
round proofs split only the 16 coordinates. This is bounded single-round
arithmetic, rather than reduction of a complete permutation or a large
recurrence cell.

The inspected RootModelCell02 has the same checkpoint structure as Cell00
and Cell01. The focused predecessors passed in about 35–38 seconds with
roughly 4.2 million KiB RSS and no swaps. No limits were raised and no failed
cell was retried. No generator or existing cell source was edited. No full
root-table certificate aggregation or release replay was launched.

These root-model prerequisites are consumed by the exact native public,
external and record association import closure. They do not by themselves
prove the native association hypotheses, a compiler return or proof-account
client success. The final remaining-module manifest identifies the still
missing part of that closure.
