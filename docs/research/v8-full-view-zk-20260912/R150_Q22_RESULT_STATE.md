# R150: exact actual query sampler result and state

The selected R137 query sampler now returns exactly the query result and
advanced transcript represented by `Q22SamplerProgram.challengeRun`, for any
explicit total byte oracle and initial state. The settings remain 22 queries,
2^18 positions and 64 draws. The source while loop is proved to terminate from
the existing symbolic progress bound; no artificial fuel result is assigned
to the source execution.

The model result is encoded back into the source result, including the complete
query vector and both draw-limit counters. No error constructor is collapsed
by a decoder. Separate source guard theorems retain the invalid-bound and
count-exceeds-bound errors and their unchanged transcript.

R137 wrapping arithmetic and R86 checked arithmetic are linked only under the
proved bounds for this execution. The squeeze functions are related explicitly,
including arbitrary raw hash failure and divergence. The public result theorem
uses the specified total byte oracle; it is not a shared-oracle probability law.

The four production leaves R147, R148, R149 and R150 compiled successfully.
Complete audits and resource evidence are retained in
`evidence/r150-q22-result-state`. The disclosed `core.fmt.Formatter` type
dependency is unchanged; there is no added proof axiom or unfinished proof.

The next proposition is the full selected callback chronology and observed
shared-oracle call history. Privacy and soundness remain open. No verifier
source or security parameter changed; the 999,790 / 999,532 CU result remains.
