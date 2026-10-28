# Stage 1 — same-prefix preparation

`NDA_DriverDomain.preparation` compiles against the retained coherent SInt2
workspace and NCU cache. From NCU's actual Prefix it derives S2, all 22 bounds
<262144, and canonical gamma, kappa, alpha[2], rho, semanticAlpha[10], claim.
No field gate is assumed; c.boundaries, c.std, c.query are unchanged.
Imports SAP_OpeningCuts/OpeningShape/SemanticCanonical/AlphaTransport; these
invert the same installed preparation and compose its arithmetic laws.
The output is mapped from the SAME retained Prepared via currentPrepared.
This is model proof only, not native/ELF association or 100-bit closure.

NDA_L001 rejected carrier-transport draft, zero credit (recovery sorryAx).
NDA_L002: target NDA_DriverDomain.lean, exit0, wall2.286053860s,
peakRSS5393720KiB, swap0, revision1d7752908191642fc8383c99bbadfb46fab8850c
plus dirty source hash57184ed11a13b6c63f6f807b0c66e66b9869c5090ce04666950f8597fb508b5c.
#print axioms preparation = [propext, Classical.choice, Quot.sound].
Exact commands/dependency hashes/cgroup limits are in NDA_ATTEMPTS.jsonl.
One scope at a time, -M7000, MemoryHigh6G/Max8G/Swap0/Tasks64; admissions exit0
and allowed:true. Retained drvdom cache reused, never removed or reseeded.
Runner copied from NCU with own workspace/prefix, and records source snapshots.
No Kani, shipped source edits, artifact rebuilds, key operations or push.

Remaining: query distinctness; coordinates, rhs, power canonicality, then leaf
composition with the exact residual premises. Budget used 2/50 Lean, 0/0 Kani.
