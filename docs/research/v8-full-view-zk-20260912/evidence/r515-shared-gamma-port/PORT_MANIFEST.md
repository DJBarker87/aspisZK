# R515 shared-gamma kernel import-only port

This scratch port preserves four existing Lean source files and their original
`AspisV8.*` namespaces and theorem bodies. Only intra-port import module names
change so the files compile at remote module paths `AspisR515SharedGamma.*`.

Dependency order: `AffinePrimal`, `QmCrossRange`, `SemanticCarry`, then
`SharedGammaDots`. The two leaves import `Mathlib.Tactic`; SemanticCarry imports
ported AffinePrimal; SharedGammaDots imports ported SemanticCarry and
QmCrossRange. No other direct source dependencies occur.

This is reusable-kernel plumbing only. It does not assert actual source
execution, shared-gamma callback correspondence, or any strengthened premise.
