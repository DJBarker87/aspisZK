# R596: selected chord core

R596 proves that selected R203 `rawData` returns the full normalized chord triple under explicit canonical coordinate, rational-coordinate, denominator, and distinct-point hypotheses. It also proves the 271-core determinant scaling identity and its nonzero equivalence under the nonzero chord scale.

## Verification

- Canonical source: `lean/AspisV8R19/R596SelectedChordCore.lean`
- Original draft: `.r21-scratch/R596SelectedChordCore.UNVERIFIED.lean`
- Canonical/draft SHA256: `a07400ba8149cac9fa4eb4b18e6c7b02898fe76c83afc9e0275ed9a3f80ef7eb` (byte-identical)
- Final canonical target receipt: `1791089481450775000`
- Source revision: `017e6f6a504a0d7d53d23a0842bf0929e5aeb16b`
- Result: exit 0; wall 1.62 s; Lean-child peak RSS 3,767,676 KiB; swap 0.
- Resources: `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`; Lean `-j1 -M4500`.
- Sole complete final `#print axioms` report uses only `[propext, Classical.choice, Quot.sound]`.

The evidence includes all five earlier focused failures (`1791089279196655000`, `1791089300759723000`, `1791089365239982000`, `1791089406253447000`, and `1791089457879347000`), with their source snapshots, logs, receipts, and axiom output. The final replacement uses symbolic determinant rewrites and an explicit nonzero multiplication proof; it does not normalize the whole field expression. Sources, direct pins, runner, publish paths, and a SHA manifest are in `evidence/r596-selected-chord-core/`. No check was rerun for this promotion.

## Boundary

R596 keeps all coordinate and denominator conditions as hypotheses. It does not derive them from the actual sampled circle chronology or bind `alpha` through the entire freeze callback. It proves no whole-G compatibility, simulator, oracle law, privacy, or security theorem.

The next required steps are to instantiate the rational coordinates and distinctness conditions from the actual selected circle chronology, bind alpha, then prove the two universal full-G compatibility identities and actual shared-oracle law.
