# R522 gamma word prefix

Final target `AspisV8R19/R522GammaWordPrefix.lean`, SHA-256
`6931c95286c748335a0dee5a78186f2b75149bbcd6a2cea0fbd971d72125dad7`,
compiled with exit 0, wall 0:01.58, peak RSS 3,707,500 KiB, and zero swap.
The exact source, receipt, raw log, and complete two `#print axioms` outputs
are preserved under `focus-records/aspis-focus-1791055168903603000.*`.

It proves a bounded four-product U64 multiply/add prefix has the expected
natural value and bound, and that the checked `Result U64` multiply/add chain
returns the corresponding wrapping result. The first changed-target failure
`1791055095976160000` is retained; it records the rejected small-power
normalization shape. No unchanged check was rerun.

This does not prove an array loop, native group execution, or complete selected
preparation routine.
