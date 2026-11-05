import NGL_MapReference.Types
set_option pp.all true
#print NGL_MapReference.VerifierError.read_discriminant
run_elab do
 let env ← Lean.getEnv
 for h : i in [0:env.header.moduleNames.size] do
  if env.header.moduleNames[i]!.toString == "NGL_MapReference.Types" then
   for c in env.header.moduleData[i]!.constants do
    Lean.logInfo m!"NIM_DECL {c.name}"
