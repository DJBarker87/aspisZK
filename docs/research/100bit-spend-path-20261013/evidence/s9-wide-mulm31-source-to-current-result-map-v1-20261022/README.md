# Attempt16 WideExact.mul_m31 M31+CM result map

This accepted focused Lean leaf proves direct same-result mapping for the extracted attempt16 `M31.mul` call to the current field M31 operation, and lifts it through the extracted `CM31.mul_m31` call. It uses the source-pinned all-word map to R22 wrapping multiplication, current R22 operation correspondence, and explicit source/current record maps. This packet does **not** claim QM31 or WideExact `mul_m31` mapping; those are separate dependent leaves.

The source cut’s exact generated function bodies and source pins are retained by the linked attempt16 packets. This proof does not claim ELF/SBF runtime refinement. `evidence/` contains the exact Lean invocation, preflight, receipt, axioms output and resource records. The transitive import closure is represented by its SHA256 and direct import pins in `dependency-pins.json`; full closure and compiled objects are excluded.
