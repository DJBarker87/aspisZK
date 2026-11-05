import NFW_ErrorReferenceTypes
set_option pp.all true
#print NFW_ErrorReference.VerifierError.read_discriminant
run_elab do
 let env ← Lean.getEnv
 for h : i in [0:env.header.moduleNames.size] do
  if env.header.moduleNames[i]!.toString == "NFW_ErrorReferenceTypes" then
   for c in env.header.moduleData[i]!.constants do
    Lean.logInfo m!"NIM_DECL {c.name}"
