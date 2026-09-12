# Source squeeze: exact fresh law or explicit prior reuse

`FSSourceSqueezeFreshOrPrior.lean` closes one interface needed by the OOD
sampler composition.  At any valid chronological oracle prefix, the two
literal source requests for a squeeze are classified as either both unseen,
in which case the already proved adaptive-pair law gives exact mass
`1 / |Block|^2`, or one of two explicit reuse cases occurs:

1. `digest ++ [1]` was seen earlier, placing the full 256-bit digest in the
   existing `priorTargets` set; or
2. `digest ++ [2]` was seen earlier, retained as a separate advance-input
   collision.

The second alternative matters: it is not a target request and therefore
cannot be hidden in `priorTargets`.  The result does not infer independence
from byte labels and does not condition cached executions away.

This is not the complete OOD law.  The two reuse alternatives still need
resource-bounded charges, and the law must be composed through the four
squeezes of every attempt, all state-changing retries, decoder rejection and
the first-point-dependent distinct sampler.  No global security number changes
at this milestone.

Focused evidence is in
`results/v8-completion-fs-extraction-20260911/source-squeeze-fresh-or-prior-v1/report.json`.
