import Aeneas
run_elab do
  let env ← Lean.getEnv
  env.constants.toList.forM fun decl => do
    let n := decl.1.toString
    if n.startsWith "Aeneas.Std" &&
        (n.endsWith ".first" || n.endsWith ".copied" ||
         n.endsWith ".starts_with" || n.endsWith ".eq") then
      Lean.logInfo m!"{decl.1}"
