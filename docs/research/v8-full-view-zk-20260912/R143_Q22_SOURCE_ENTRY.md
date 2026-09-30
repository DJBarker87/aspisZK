# R143/R145: actual q22 source entry and inner scan

The retained R137 extraction now compiles in the main Lean 4.32 workspace.
Its entry uses count 22, bound 2^18, and maximum 64 draws. All three source
query-error constructors remain unchanged. The original generated artifacts
and the source snapshot are retained alongside the compatibility adaptations.

The fixed entry is proved to call its generated outer loop with those exact
parameters. The inner loop is proved equal to the existing word-scan model
for every finite list of four-byte words, provided the current draw count is
at most 64. The checked increment and actual wrapping increment are proved
equal whenever the source increments. Vector failure and divergence branches
are preserved. No namespace equivalence is assumed.

The four focused targets exited successfully; their logs, durations, peak
process RSS, swap, source revision/digests, and full axiom audits are in
`evidence/r143-q22-extraction/manifest.json`. The cached Aeneas formatting
type `core.fmt.Formatter` appears in the query method/loop audits and is
recorded explicitly. No `sorryAx` appears.

The next proposition is the actual R137 outer squeeze/scan loop and public
value/error/state equality to `Q22SamplerProgram.challengeRun`. Ordered
shared-oracle history, privacy, and soundness remain open. No verifier source
or security parameter changed; no CU benchmark or regression suite was run.
