# R586: independent sampler state

R586 proves the specified state-independence fact for the independent program interpreter. For every budget, start states `s` and `s'`, fixed cached block `b`, cursor index `j : Fin 9`, and observer `f : Option Nat → State → Fin 9 → ℚ`, the `independentMean` of `limbProgram budget ⟨s,b,j⟩` equals that of `limbProgram budget ⟨s',b,j⟩` when the observer reads only the result, returned cached block, and returned index.

The proof is by budget induction. At cursor index 8, it expands the two independently uniform squeeze asks. At other indices, acceptance reduces directly and rejection invokes the induction hypothesis. The observer intentionally omits returned transcript state and the oracle trace.

## Verification

- Canonical source: `lean/AspisV8R19/R586IndependentSamplerState.lean`
- Original draft: `.r21-scratch/R586IndependentSamplerState.UNVERIFIED.lean`
- Canonical/draft SHA256: `b9dfe8dba6e734aca5b730a0ce0015f0483a7b6036f1078dd7e94e39e98643f3` (byte-identical)
- Final canonical-module-path receipt: `1791087117467108000`
- Source revision: `9cec79766c6977ae93e2b2bc458532b9b6888611`
- Final result: exit 0; wall 1.27 s; Lean-child peak RSS 3,254,996 KiB; swap 0.
- Resources: `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`; Lean `-j1 -M4500`.
- Complete final `#print axioms`: `[propext, Classical.choice, Quot.sound]`.

Five failed focused attempts, the first green run with its unused-simp warning, and the final clean green run are retained with their exact source snapshots, logs, receipts, direct dependency copies, runner, and recursive SHA manifest in `evidence/r586-independent-sampler-state/`. No Lean job was rerun for this promotion. `PUBLISH_PATHS.json` records the exact canonical file, report, and evidence paths.

## Boundary

This is an independent-program fact for the specified output-only observer. It does not establish `FreshFrom`, a shared-oracle law, source call-trace equality, native generated execution, privacy, or security.

The first remaining proposition is the complete ordinary challenge independent-block/tape law, followed by actual memoized shared-oracle collision and adaptive retry losses. R584 supplies the independent block-program correspondence; it does not establish that the shared oracle has this law.
