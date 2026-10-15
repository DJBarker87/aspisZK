import R1SemanticHit

-- Import-only diagnostic against the retained original dependency objects.
run_cmd do
  let owner ← Lean.findModuleOf? `R0P.Mask.decisionZ.congr_simp
  Lean.logInfo m!"decisionZ.congr_simp owner: {owner}"
