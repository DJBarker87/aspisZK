# Attempt16 QM31/WideExact `mul_m31` full Result map

This focused Lean leaf extends the accepted attempt16 M31+CM result map through the actual extracted `QM31.mul_m31` and `WideExact.mul_m31` bodies. It proves full Result equality under the source-to-current carrier maps, including failure and divergence behavior. The helper `current_qm_mul_m31_eq_map` states its scalar argument in the original M31 carrier so the upper WideExact bind uses the exact mapped-call shape.

The source cut and its arithmetic bodies are pinned by the linked attempt16 source-cut packets; this theorem is a generated-source-to-current-operation map, not an ELF/SBF runtime refinement. The exact target, toolchain, import pins, invocation, preflight, receipt, axioms, and resource records are retained here. The transitive compiled closure and compiled objects are excluded.

The four `#print axioms` reports contain only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`; `bind_mapR` has no axioms.
