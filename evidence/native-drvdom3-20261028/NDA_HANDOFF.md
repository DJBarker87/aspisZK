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

# Stage 2 — distinct queries and primitive-domain composition

`NDA_DriverDomain.query_distinct` derives an injective Fin22→Fin262144
and exact coordinate equality to THIS cut's 22 query words. It uses the
installed query arithmetic/strict decoder, not fresh sampled queries.
L003 exit0,3.508835574s,RSS5349540KiB,swap0.

`NDA_QueryCanonical` weakens the existing arithmetic ports to canonicality
preservation only, proves one actual native-model query iteration, induction
on Port2_QueryLoop.Calls, and on_prefix for NCU's own query result.
No buffer execution is assumed. `retained` proves op2/op3/op9/op16 of
Tx1Q_QueryBridge.leaves are c.query's unchanged slots. `of_ports` maps the
existing stronger ports to these laws, not vice versa. These primitive laws
are explicit remaining obligations, not new trust or a closed instance.
L004 generic step/induction passed; L005 rejected reserved-keyword name draft;
L006 complete module exit0,2.342826512s,RSS5385104KiB,swap0.

`NDA_CircleCanonical.on_prefix` propagates a law on c.boundaries.circle to the
four coordinates of THIS Prepared. It inverts the same successful semantic
verification, derives both circle invocations, and retains the same z array.
`of_source` supplies that primitive law IF the retained slot equals the
existing emitted wrapper; it never installs a replacement dictionary.
L007 exit0,2.568761469s,RSS5399024KiB,swap0.
All successful roots print only [propext,Classical.choice,Quot.sound].
Aeneas objects resolved by the ordered LEAN_PATH are pinned (221 object/split
files) in NDA_AENEAS_PINS.json. All direct imports are re-pinned per attempt.
The cache already existed, so no seed was copied or modified beyond NDA objects.
Budget used 7/50 Lean, 0 Kani. Remaining: exact reduced domain/leaf export,
and determine whether the arbitrary primitive-slot laws are derivable.
