
/-! Stage B driver (native tool). Imports NPO_CloneNov (the 10 November re-instantiation, via
TAS_FinalB) and NPP_ComputableSdk; adds the `nov_eq` equations of the 12 id-dependent copies and

  NPP_SdkNovEq.eq : ∀ {W Tx} (c : NNH_HostCtx.Ctx W Tx),
    NPP_C.AspisR1.NOC_Run5bCtx.sdk c = NPO_Nov.AspisR1.NOC_Run5bCtx.sdk c

each sent to the kernel by `addDecl`; writes NPP_SdkNovEq.olean (no IR; proofs only). -/
open Lean Meta in
def NPP.novMain (outDir : String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{module := `NPO_CloneNov}, {module := `NPP_ComputableSdk}] {} (trustLevel := 1024) (loadExts := false)
  let ctx : Core.Context := { fileName := "NPP_SdkNovEq", fileMap := default, maxHeartbeats := 0 }
  let st : Core.State := { env := env.setMainModule `NPP_SdkNovEq }
  let act : MetaM UInt32 := do
    let (eqs, failed) ← NPP.stageB `AspisR1.NOC_Run5bCtx.sdk (NPP.Inputs.toSet NPP.Inputs.cand)
      (NPP.Inputs.toSet NPP.Inputs.leaves) NPP.Inputs.ids (NPP.Inputs.toSet NPP.Inputs.idDep) `NPP_C `NPO_Nov
    NPP.log <| Json.mkObj [("event","stageB"),("eqs", toJson (eqs.map toString)),("failed", toJson (failed.map toString))]
    if !failed.isEmpty then return 2
    let h := mkConst `NPP_C.AspisR1.NOC_Run5bCtx.sdk.nov_eq
    let some ci := (← getEnv).find? `NPO_Nov.AspisR1.NOC_Run5bCtx.sdk | return 3
    let (ty, pf) ← forallTelescope ci.type fun xs _ => do
      let mut p := h
      for x in xs do p ← mkCongrFun p x
      let lhs := mkAppN (mkConst `NPP_C.AspisR1.NOC_Run5bCtx.sdk) xs
      let rhs := mkAppN (mkConst `NPO_Nov.AspisR1.NOC_Run5bCtx.sdk) xs
      return (← mkForallFVars xs (← mkEq lhs rhs), ← mkLambdaFVars xs p)
    addDecl (.thmDecl { «name» := `NPP_SdkNovEq.eq, levelParams := [], type := ty, value := pf })
    NPP.log <| Json.mkObj [("theorem", toJson "NPP_SdkNovEq.eq"), ("type", toJson (← ppExpr ty).pretty)]
    for n in eqs.push `NPP_SdkNovEq.eq do
      let ax ← collectAxioms n
      NPP.log <| Json.mkObj [("axioms", toJson n.toString), ("value", toJson (ax.map toString))]
    return 0
  let (code, st') ← (act.run' {} {}).toIO ctx st
  if code != 0 then return code
  writeModule st'.env s!"{outDir}/NPP_SdkNovEq.olean" (writeIR := false)
  NPP.log <| Json.mkObj [("event","written"),("module","NPP_SdkNovEq")]
  return 0

def main (args : List String) : IO UInt32 := NPP.novMain (args.headD "out")
