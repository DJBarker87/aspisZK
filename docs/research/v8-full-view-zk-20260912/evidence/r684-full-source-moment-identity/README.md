# R684 full source moment identity — scratch evidence

Target: `AspisV8R19/R684FullSourceMomentIdentity.lean`.

Final focused run `1791119479876262000` compiled the exact final source with exit 0, wall time 1.23s, peak Lean-child RSS 3,290,600 KiB, and zero swaps. The complete `#print axioms` output is `[propext, Classical.choice, Quot.sound]`.

The theorem is a field-model identity. It connects the two selected full 256-block coefficient boundary rows to the complete source pairing over `flattenFull q`. It keeps the structured `TwoSwapSourceG.original (finishCoins ...)` pairing, all three point terms, inactive balance, and the ordinary/structured tau image terms. It does not establish source execution, legal-witness compatibility, any oracle law, a simulator, privacy, or security.

The first remaining proposition is the actual legal-H1 / same-public target construction that supplies these full source conditions, followed independently by the causal shared-oracle and publication-simulator obligations.

Rejected focused attempts are retained under `attempts/`; they reflect only rewrite/order plumbing and are not proof results.
