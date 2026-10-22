# Prover commitment continuation 32

Base: 26b922be6. Branch: codex/cx-prover-commit32-20261022.
Work in progress. Target not yet established.

D143/D144 govern this continuation: sorted owned association lists and small
recursive extracted functions; public statement bytes, submitted proof bytes,
and answers to adversary queries are the observable. Timing and other side
channels are outside the privacy contract. Internal programming tables and
attempt counts are not published protocol outputs.

Stage 1 starts with sorted numeric-map insertion, lookup and query-order
publication. These are proof-only references; no native-owner equality is
claimed merely by adding them. The remaining stages are the complete
publication driver, eight-attempt owner, real entropy/reservation owner,
source-to-FSExperiments conversion, both WholeRunJoins and deletion-only
endpoint specialisation. RustProverRefinement remains explicit.
