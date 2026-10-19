# Executable recovery caller candidate snapshot (2026-10-19)

**Pending consumer checks.** This directory is a candidate-source snapshot, not the canonical `lean/` tree and not a complete release claim. Each file has an exact source hash, direct imports, and status in `source-manifest.json`. Green prerequisites have canonical receipt paths there; all other entries remain uncompiled/unverified candidates.

## Dependency order

Follow `source-manifest.json` `dependency_order`. The order starts with the fixed-input decoder family and literal constructors, then encoder/degree and image-filter bridges, runtime-distance filtering, witness recovery and joint keep refinement, and the second-fold sparse-projection caller. `SecondFoldSparseProjectionCore-v3` is a green prerequisite; `SecondFoldSparseProjectionBridge-v4` and the concrete five-lane projection consumer remain candidates.

## Remaining exact premises and checks

- Compile the literal input constructors and initial/final runtime evaluator bridge against the coherent native owner closure. The runtime evaluator must equal the released exact encoder at every coordinate.
- Compile the degree bridge and image-filter/witness consumers. Their exact interpolation witness, root-candidate contract, message degree bounds, and close predicate are still explicit theorem inputs.
- Compile the runtime joint-keep consumer and verify it refines the existing `selectedSupport` and `IncrementalCandidateLoop` semantics while the list algorithm remains computable.
- Compile the current final-five-lane sparse projection bridge. It requires each distinct repeated channel word's successful decoder output and makes no equality assumption between the four channel words.
- Only after these focused targets pass should the full composition be considered; this packet alone does not establish end-to-end extractor completeness or release evidence.
