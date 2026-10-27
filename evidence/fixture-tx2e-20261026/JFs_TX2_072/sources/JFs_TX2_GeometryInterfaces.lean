import SAQ_GeometrySource
run_cmd do
  for (n,_) in (← Lean.getEnv).constants.toList do
    if n.toString.startsWith "R17CurrentDomainSource." || n.toString.startsWith "R17CurrentDomainCanonical." then
      Lean.logInfo m!"{n}"
#print AspisR1QueryGeometryActual.fast_domain.fibre_point
#print R17FibrePointLineNodeActual.line_node
#print R17CurrentCM31Semantics.operations
