
/-! Stage B for the model cone (native tool). Imports NPO_CloneNov and NPP_ComputableModel (the
four-root stage-A olean of NPP_L060); adds `nov_eq : NPP_C.X = NPO_Nov.X` for the id-dependent
copies (kernel-checked by `addDecl`), and `NPP_C.LIBC_BatchMerkle.returns` transported from
`NPO_Nov.LIBC_BatchMerkle.returns` along the equations (not re-checked). Writes NPP_ModelNovEq.olean. -/
open Lean Meta in
unsafe def NPP.modelNovMain (outDir : String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{module := `NPO_CloneNov}, {module := `NPP_ComputableModel}] {} (trustLevel := 1024) (loadExts := true)
  let ctx : Core.Context := { fileName := "NPP_ModelNovEq", fileMap := default, maxHeartbeats := 0 }
  let st : Core.State := { env := env.setMainModule `NPP_ModelNovEq }
  let act : MetaM UInt32 := do
    let mut all : Array Name := #[]
    for r in NPP.Inputs.roots do
      let (eqs, failed) ← NPP.stageB r.toName (NPP.Inputs.toSet NPP.Inputs.cand)
        (NPP.Inputs.toSet NPP.Inputs.leaves) NPP.Inputs.ids (NPP.Inputs.toSet NPP.Inputs.idDep) `NPP_C `NPO_Nov
      NPP.log <| Json.mkObj [("event","stageB"),("root", toJson r),("eqs", toJson eqs.size),("failed", toJson (failed.map toString))]
      all := all ++ eqs
    let (_, dep) ← NPP.walk (← getEnv) `NNH_ReturnsBundle.tx1Value (NPP.Inputs.toSet NPP.Inputs.cand)
      (NPP.Inputs.toSet NPP.Inputs.leaves) NPP.Inputs.ids
    let tr ← NPP.transportNov `LIBC_BatchMerkle.returns (dep.getD · false) (NPP.Inputs.toSet NPP.Inputs.idDep)
    let names := all ++ (tr.map (#[·])).getD #[]
    let mut axs : Std.HashSet String := {}
    for n in names do
      for a in ← collectAxioms n do axs := axs.insert a.toString
    NPP.log <| Json.mkObj [("event","done"),("nov_eq", toJson all.size),("transported", toJson (tr.map toString)),("axioms", toJson axs.toList)]
    return 0
  let (code, st') ← (act.run' {} {}).toIO ctx st
  if code != 0 then return code
  writeModule st'.env s!"{outDir}/NPP_ModelNovEq.olean" (writeIR := false)
  NPP.log <| Json.mkObj [("event","written"),("module","NPP_ModelNovEq")]
  return 0

unsafe def main (args : List String) : IO UInt32 := NPP.modelNovMain (args.headD "out")
