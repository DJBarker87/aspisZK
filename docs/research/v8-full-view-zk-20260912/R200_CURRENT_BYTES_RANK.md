# R200 current byte-loop rank decrease

[R200CurrentBytesRank.lean](lean/AspisV8R19/R200CurrentBytesRank.lean) proves a strict rank decrease for every actual current byte-loop body result of the form `.ok (.cont (iter1, b1))`. The rank is the remaining number of slice elements, `iter.iter.slice.val.length - iter.iter.i`. The only premise is that exact continuation equation; the theorem makes no assumption that the complete loop succeeds and preserves the boundary around error results.

The focused compile used source revision `34382b2ee70a75cb902f687cab291354ea3101af` and has only the reported Lean foundation axioms. Run metrics, all four failed attempts, exact source copies, and checksums are in [the R200 evidence bundle](evidence/r200-current-bytes-rank/manifest.json).

The next step is to apply this rank result and the R198 body mapper to prove the finite current byte-loop mapper and full `bytes` entry correspondence. `Vec.extend`, selected gamma-fold chronology, full-freeze execution, and security remain outside this result.
