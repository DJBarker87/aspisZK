# R240 selected half and scalar multiplication execution

`AspisV8R19/R240HalfExecution.lean` compiled successfully. For arbitrary raw U32, the selected M31.half returns the exact R228 half word. On canonical encodings it returns x/2; selected CM31.half returns z/2; selected CM31.mul_m31 returns z times the embedded base scalar. No opaque execution premise is added. The raw dependency explicitly records the two shift-literal API adaptations and ground count equalities.

Compile revision `f3ffde1f52bab63d1d561515f06978c2bb097291`; exit 0; wall 0:01.57; child peak RSS 3709904 KiB; swaps 0. All complete axiom reports contain only propext, Classical.choice and Quot.sound (subsets allowed). No sorryAx, native decision axiom or execution assumption is admitted. Pinned Lean 4.32, `-j1 -M4500`, 5/7 GiB zero-swap scope. Complete evidence is in [the manifest](evidence/r240-current-half-execution/manifest.json).

First remaining proposition: Bind actual coefficient-array execution, the selected point-derived t value, and both private R110 and fallback inverse routes.

Full callback chronology, joint privacy and soundness remain open. Verifier source, security parameters and 999,790 / 999,532 CU results remain preserved. No benchmarks or unchanged regression suites reran.
