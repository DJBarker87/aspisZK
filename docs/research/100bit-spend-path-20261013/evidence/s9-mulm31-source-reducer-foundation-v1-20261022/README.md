# S9 M31 source reducer foundation

This source-only packet preserves three centrally checked Lean leaves for the attempt16 genuine `WideExact.mul_m31` source cut: the literal `wrapping_shr`/bitvector shift equality, the source-shaped reducer fold mapped to the existing R22 wrapping fold, and the actual generated reducer mapped to a source-shaped wrapping result. The actual extracted scalar-source reducer is now proved to return the same result as `R22CurrentReducerMul.wrappingReduce`, including both folds and the final guarded subtraction. The higher-level `WideExact.mul_m31` result map remains open.

The attempt16 source and extraction provenance are retained in [`s9-wide-mul-m31-source-attempt16-v1-20261022`](../s9-wide-mul-m31-source-attempt16-v1-20261022/). These leaves consume the normalized Aeneas source owner and existing R22 model; they do not claim SBF MIR equivalence or complete `WideExact.mul_m31` refinement.

Each `runs/` directory contains the exact source revision, command, closure preflight, receipt, Lean log, and resource profile for one focused target. Compiled objects are intentionally excluded. The manifest hashes every retained file, and `check_packet.py` verifies the manifest and rejects compiled objects or caches.
