import JFs_TX2_PointShift
run_cmd do
  let env ← Lean.getEnv
  if let some ci := env.find? `AspisR1QueryGeometryActual.fast_domain.TABLE_A then
    if let some val := ci.value? then
      for n in val.getUsedConstants do
        if n.toString.contains 'T' then Lean.logInfo m!"{n}"
