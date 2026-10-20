# Candidate sampler output canonicality

This focused Lean target proves that successful candidate `decode8` and `ordinary_sample` outputs have all eight U32 limbs strictly below `P = 2147483647`. It follows the actual generated `canonical_qm31`, `WideExact.new`, array-index, and ordinary-sample wrapper calls.

The target is candidate-only. It does not specialize the generic Prepared callback, establish production-source equivalence or runtime adoption, or prove a sampler distribution theorem. The output coordinates are stated in the extracted candidate `WideExact` carrier.

The manifest pins the exact Lean source, direct import sources and objects, NUC receipt, command, preflight, logs, toolchain, and standard axiom report. No object files are included.
