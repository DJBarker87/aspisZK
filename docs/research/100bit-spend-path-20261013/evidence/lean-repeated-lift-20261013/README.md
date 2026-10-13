# RepeatedLift focused Lean receipt

This is a focused compile of the abstract repeated-support/projection lemmas in
`lean/RepeatedLift.lean`. It does not instantiate the premises with the concrete
E256 encoder and is not a protocol or security result.

- Target: `R1RepeatedLift` (`R1RepeatedLift.lean`)
- Pinned workspace: `/home/dombarker/project-offloads/aspis-fs-generic-20261006`
- Command: `./run2.sh repeated-lift-r1-20261013e R1RepeatedLift 5000 6`
- Scope: `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`
- Exit: 0; wall time 0.82 s; maximum RSS 1,675,288 KiB; swap 0
- Source SHA-256: `bb5fa533f56b5b9c7adc84970cad149dfb0e4eccab4820f8fa4cbea74a996605`
- Repository revision: `628054cd494c66dc91e4e01612c70bd164ecf276` (source added after this checkpoint)
- Axioms for all five printed lemmas: `[propext, Classical.choice, Quot.sound]`
- Environment manifest SHA-256: `ad7b87bbcfd84dc762927729c3d35a1822a530e57538a58c9d559f6ec4b6754e`
- Focused runner SHA-256: `15e6cb788a5b69473c67456c71d1add7b6fe016bf0417ec68cbe2bee0549c9e2`

The complete attempt evidence is retained under `remote-evidence/`, including
the four earlier failed plumbing attempts A-D and successful attempt E, their
logs, source snapshots, SHA receipts, and `/usr/bin/time -v` receipts. Attempts
A-D failed before producing an olean; E compiled the source snapshot whose hash
matches the local source above. The remaining warnings are unused-section-variable
warnings only.
