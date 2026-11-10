import NPP_ComputableSdk
/-! NPP_ negative control for the leanchecker replay (nothing imports this module).
`NPP_Teeth.bad` claims the computable copy equals the ORIGINAL default-id dictionary,
`@NPP_C.AspisR1.NOC_Run5bCtx.sdk = @AspisR1.NOC_Run5bCtx.sdk`, with the proof term of a different
equation (`NPP_C.AspisR1.DrvC_Installation.sdk.npp_eq`). The kernel must reject it when checked; it is
then added with `debug.skipKernelTC` so the olean carries one ill-typed declaration, and a replay with
teeth must reject the module. `NPP_Teeth.good` is a correct equation of the same family. -/
open Lean Meta in
run_meta do
  let lhs := mkConst `NPP_C.AspisR1.NOC_Run5bCtx.sdk
  let rhs := mkConst `AspisR1.NOC_Run5bCtx.sdk
  let ty ← mkEq lhs rhs
  let bad : Declaration := .thmDecl { «name» := `NPP_Teeth.bad, levelParams := [], type := ty, value := mkConst `NPP_C.AspisR1.DrvC_Installation.sdk.npp_eq }
  let goodTy := (← getEnv).find? `NPP_C.AspisR1.DrvC_Installation.sdk.npp_eq |>.map (·.type) |>.get!
  addDecl (.thmDecl { «name» := `NPP_Teeth.good, levelParams := [], type := goodTy, value := mkConst `NPP_C.AspisR1.DrvC_Installation.sdk.npp_eq })
  let env0 ← getEnv
  try
    addDecl bad
    IO.println "UNEXPECTED: kernel accepted NPP_Teeth.bad"
  catch _ => IO.println "NPP_TEETH kernel rejects bad when checked (expected)"
  setEnv env0
  withOptions (fun o => debug.skipKernelTC.set o true) (addDecl bad)
  IO.println s!"NPP_TEETH bad added unchecked: {(← getEnv).contains `NPP_Teeth.bad}"
