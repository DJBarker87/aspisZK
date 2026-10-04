# R687 actual combine-beta composition

R687 conditionally composes successful selected `r55_decode_into` calls with the actual four-slot `combine_beta` wrapper. Given successful decodes for the 104-word C1 and 48-word C2 inputs, and canonical coefficient-word bounds for `powers.c1_limbs` and `powers.mixed`, it constructs the returned selected `laneArray`. All 16 lanes are below `P = 2^31 - 1`; every lane equals the exact selected 38-term expression: 26 C1-chunk products plus 12 source-indexed C2 products, modulo `P`.

The proof derives decoded-array canonicality from actual successful decoder executions using R635, restricts C1 through the exact R677 chunk routing, applies R616 to each of the 16 limbs, and uses R663 to compose the actual wrapper. It retains the conditional decoder-success boundary: it does not prove a successful decode, erase decoder errors, prove a full quotient serialization, or prove the whole callback, privacy, or security.

Final focused run: `1791121456904155000`, exit 0, wall 2.09 s, peak Lean-child RSS 3,773,584 KiB, swap 0. Source revision `85789d10e9e85f37dd616e08f0ac9de66b4937d1`; source SHA-256 `ca7871b65858bcaf3af6ea5cf70f0c16118140d924dcaaa04564a616de4d3b67`. Pinned Lean 4.32 cache with `-j1 -M4500`, `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, and `TasksMax=128`.

The final axiom report is `[propext, Classical.choice, Quot.sound, Aeneas.Std.core.fmt.Formatter]`. `Formatter` is inherited through R635 and R663; its exact provenance is recorded in [FORMATTER_PROVENANCE.md](evidence/r687-combine-beta-composition/FORMATTER_PROVENANCE.md). Native adequacy of that capture path remains open.

Preserved attempts: `1791121246338609000` failed before the R616 import and correct membership plumbing; `1791121393154690000` failed on `List.getElem_mem` syntax; `1791121410650458000` established the canonical-limb subgoal but was superseded when the required exact 38-term equality was added; `1791121456904155000` is final. Formatter diagnostics are retained separately and are not proof attempts.

The next missing bridge is the mathematical packed serialization and full quotient composition; this result does not close source callback, oracle, privacy, or soundness obligations.
