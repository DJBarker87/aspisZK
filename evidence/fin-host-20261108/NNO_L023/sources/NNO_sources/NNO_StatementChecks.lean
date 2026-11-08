import Lean
import NFA_WALKER
import NFA_MemoryLimit
import NNM_COMBINED_IMPORT
import TAS_Top
import NVR_COMBINED_IMPORT
import NVR_Carrier
import NVR_DispatchEmitted
import NVR_Reify
import NVR_NNCWeak
import FIN_COMBINED_IMPORT
set_option autoImplicit false
noncomputable section
namespace NNO_StatementChecks
open RSL

def statementOf {P : Prop} (_ : P) : Prop := P

theorem statement240 (a2 : NMV_ConcreteWindows.Allocation) (ch : NMX_R4_Authentication.Choices) :
 statementOf (FIN_240.candidate ch a2) =
 TX2_240.RowSpec_240 LIBB_PoolLib.library LIBB_PoolLib.deployed LIBB_V2Star.library
  (NMV_ConcreteWindows.stage2 a2 (NMX_R9_StageTwo.stage2 ch)) := rfl

theorem statement221 (a2 : NMV_ConcreteWindows.Allocation) (ch : NMX_R4_Authentication.Choices) :
 statementOf (FIN_221.candidate ch a2) =
 TX2_221.RowSpec_221 LIBB_PoolLib.library LIBB_PoolLib.deployed LIBB_V2Star.library
  (TX1_344.asStage1 LIB_Instances.VL LIB_Instances.P LIB_Instances.C)
  (NVR_Dispatch.process AspisR1.NNG_Candidate344.producer (FIN_240.producer ch a2)) := rfl

theorem statement333 (a2 : NMV_ConcreteWindows.Allocation) (ch : NMX_R4_Authentication.Choices) :
 statementOf (FIN_333.candidate ch a2) =
 TX1_333.RowSpec_333 LIBB_PoolLib.library LIBB_PoolLib.deployed LIBB_V2Star.library
  LIB_Instances.VL LIB_Instances.P LIB_Instances.C
  (NVR_Dispatch.process AspisR1.NNG_Candidate344.producer (FIN_240.producer ch a2)) := rfl

theorem statement213 (a2 : NMV_ConcreteWindows.Allocation) (ch : NMX_R4_Authentication.Choices) :
 statementOf (FIN_213.candidate ch a2) =
 TX2_213.RowSpec_213 LIBB_PoolLib.library LIBB_PoolLib.deployed LIBB_V2Star.library
  (TX1_344.asStage1 LIB_Instances.VL LIB_Instances.P LIB_Instances.C)
  (NVR_Dispatch.entry (NVR_Dispatch.process AspisR1.NNG_Candidate344.producer
   (FIN_240.producer ch a2))) := rfl

theorem statement330 (a2 : NMV_ConcreteWindows.Allocation) (ch : NMX_R4_Authentication.Choices) :
 statementOf (FIN_330.candidate ch a2) =
 TX1_330.RowSpec_330 LIBB_PoolLib.library LIBB_PoolLib.deployed LIBB_V2Star.library
  LIB_Instances.VL LIB_Instances.P LIB_Instances.C
  (NVR_Dispatch.entry (NVR_Dispatch.process AspisR1.NNG_Candidate344.producer
   (FIN_240.producer ch a2))) := rfl

theorem child240 (a2 : NMV_ConcreteWindows.Allocation) (ch : NMX_R4_Authentication.Choices) :
 FIN_240.producer ch a2 = NMV_ConcreteWindows.stage2 a2 (NMX_R9_StageTwo.stage2 ch) := rfl

theorem child344 : AspisR1.NNG_Candidate344.producer =
 NMV_ConcreteWindows.stage1 AspisR1.NNG_Candidate344.allocation
  AspisR1.NNG_TotalProducer345.producer := rfl

theorem process221 (a2 : NMV_ConcreteWindows.Allocation) (ch : NMX_R4_Authentication.Choices) :
 FIN_221.producer ch a2 = NVR_Dispatch.process AspisR1.NNG_Candidate344.producer
  (FIN_240.producer ch a2) := rfl

theorem process333 (a2 : NMV_ConcreteWindows.Allocation) (ch : NMX_R4_Authentication.Choices) :
 FIN_333.producer ch a2 = NVR_Dispatch.process AspisR1.NNG_Candidate344.producer
  (FIN_240.producer ch a2) := rfl

theorem deployed_same : LIBB_PoolLib.deployed = LIB_Instances.D := rfl

def installed (ch : NMX_R4_Authentication.Choices) (a2 : NMV_ConcreteWindows.Allocation)
 (I : TAS.Impl LIBB_PoolLib.library LIBB_V2Star.library LIB_Instances.VL) :=
 { I with process := FIN_333.producer ch a2, entry := FIN_330.producer ch a2 }

theorem tas333 (a2 : NMV_ConcreteWindows.Allocation) (ch : NMX_R4_Authentication.Choices)
 (I : TAS.Impl LIBB_PoolLib.library LIBB_V2Star.library LIB_Instances.VL) :
 TX1_333.RowSpec_333 LIBB_PoolLib.library LIBB_PoolLib.deployed LIBB_V2Star.library
  LIB_Instances.VL LIB_Instances.P LIB_Instances.C (FIN_333.producer ch a2) =
 TX2_221.RowSpec_221 LIBB_PoolLib.library LIBB_PoolLib.deployed LIBB_V2Star.library
  (TX1_344.asStage1 LIB_Instances.VL LIB_Instances.P LIB_Instances.C) (FIN_221.producer ch a2) :=
 TAS.row333_is_221 (L := LIBB_PoolLib.library) (D := LIBB_PoolLib.deployed)
  (VL := LIB_Instances.VL) (P := LIB_Instances.P) (C := LIB_Instances.C)
  (I := installed ch a2 I) LIBB_V2Star.library

theorem tas330 (a2 : NMV_ConcreteWindows.Allocation) (ch : NMX_R4_Authentication.Choices)
 (I : TAS.Impl LIBB_PoolLib.library LIBB_V2Star.library LIB_Instances.VL) :
 TX1_330.RowSpec_330 LIBB_PoolLib.library LIBB_PoolLib.deployed LIBB_V2Star.library
  LIB_Instances.VL LIB_Instances.P LIB_Instances.C (FIN_330.producer ch a2) =
 TX2_213.RowSpec_213 LIBB_PoolLib.library LIBB_PoolLib.deployed LIBB_V2Star.library
  (TX1_344.asStage1 LIB_Instances.VL LIB_Instances.P LIB_Instances.C) (FIN_213.producer ch a2) :=
 TAS.row330_is_213 (L := LIBB_PoolLib.library) (D := LIBB_PoolLib.deployed)
  (VL := LIB_Instances.VL) (P := LIB_Instances.P) (C := LIB_Instances.C)
  (I := installed ch a2 I) LIBB_V2Star.library

#print axioms statement240
#print axioms statement221
#print axioms statement333
#print axioms statement213
#print axioms statement330
#print axioms child240
#print axioms child344
#print axioms process221
#print axioms process333
#print axioms deployed_same
#print axioms tas333
#print axioms tas330
#print axioms NVR_NoWritePool.ofCloned_free
#print axioms NVR_NoWritePool.data_free
#print axioms NVR_NoWritePool.verifierCheckpoint_free
end NNO_StatementChecks
end

open Lean Elab Command
set_option pp.all true
run_cmd do
 let manifest ← IO.ofExcept (Json.parse (← IO.FS.readFile "NNO_NVR_ROOTS.json"))
 let roots ← IO.ofExcept (manifest.getObjValAs? (Array String) "roots")
 let env := (← getEnv).setExporting false
 for root in roots do
  let declName := root.toName
  let some c := env.find? declName | throwError "missing required root {root}"
  let some idx := env.getModuleIdxFor? declName | throwError "missing owner {root}"
  let statement ← liftTermElabM (PrettyPrinter.ppExpr c.type)
  let row := Json.mkObj [("root",toJson root),("owner_module",toJson env.header.moduleNames[idx]!.toString),("obligation_statement",toJson statement.pretty)]
  logInfo m!"NNO_OWNER {row.compress}"

namespace NNO_Scan
/-- Include recursor reduction rules and constant-name metadata, not only values. -/
def referenceNames (c : ConstantInfo) : Array Name := Id.run do
 let mut refs := c.type.getUsedConstants ++ ((c.value? true).map Expr.getUsedConstants).getD #[]
 match c with
 | .defnInfo v => refs := refs ++ v.all.toArray
 | .thmInfo v => refs := refs ++ v.all.toArray
 | .opaqueInfo v => refs := refs ++ v.all.toArray
 | .inductInfo v => refs := refs ++ v.ctors.toArray ++ v.all.toArray
 | .ctorInfo v => refs := refs.push v.induct
 | .recInfo v =>
  refs := refs ++ v.all.toArray
  for rule in v.rules do refs := refs.push rule.ctor ++ rule.rhs.getUsedConstants
 | _ => pure ()
 return refs
/-- Same stable first-occurrence projection as NER_ModuleTables.inspect. -/
def canonicalImports (xs : Array String) : Array String := Id.run do
 let mut result := #[]
 for x in xs do
  if !result.contains x then result := result.push x
 return result
def importsMatch (actual expected : Array String) : Bool := canonicalImports actual == expected
/-- Serialized module tables also carry reproducible theorem-cache entries.
Compare their complete declaration shape; theorem proofs are irrelevant only
when their types, levels and mutual metadata agree structurally. -/
def quotTag : QuotKind → Nat
 | .type => 0 | .ctor => 1 | .lift => 2 | .ind => 3
def sameDeclaration (a b : ConstantInfo) : Bool :=
 match a,b with
 | .axiomInfo x,.axiomInfo y => x == y
 | .defnInfo x,.defnInfo y => x == y
 | .thmInfo x,.thmInfo y => x.toConstantVal == y.toConstantVal && x.all == y.all
 | .opaqueInfo x,.opaqueInfo y => x == y
 | .ctorInfo x,.ctorInfo y => x == y
 | .recInfo x,.recInfo y => x == y
 | .quotInfo x,.quotInfo y => x.toConstantVal == y.toConstantVal && quotTag x.kind == quotTag y.kind
 | .inductInfo x,.inductInfo y =>
   x.toConstantVal == y.toConstantVal && x.numParams == y.numParams &&
   x.numIndices == y.numIndices && x.all == y.all && x.ctors == y.ctors &&
   x.numNested == y.numNested && x.isRec == y.isRec && x.isUnsafe == y.isUnsafe &&
   x.isReflexive == y.isReflexive
 | _,_ => false
/-- Inspect each module's own declarations against the checked private environment. -/
def loadedScan (env : Environment) (output : System.FilePath)
    (expected : Std.HashMap String (Array String)) : IO Bool := do
 let env := env.setExporting false
 let out ← IO.FS.Handle.mk output .write
 let mut failed := false
 let mut owners : Std.HashMap Name Name := {}
 for h : idx in [0:env.header.moduleNames.size] do
  let n := env.header.moduleNames[idx]
  let data := env.header.moduleData[idx]!
  let mut dangling : Array Json := #[]
  let mut duplicateOwners : Array Json := #[]
  let mut cachedReplicas : Array Json := #[]
  let mut edges := 0
  for declared in data.constants do
   let some c := env.checked.get.find? declared.name | do
    dangling := dangling.push (Json.mkObj [("parent",toJson declared.name.toString),("missing",toJson declared.name.toString),("phase",toJson "own_declaration")])
    continue
   if let some prior := owners[declared.name]? then
    let row := Json.mkObj [("name",toJson declared.name.toString),("previous",toJson prior.toString),("current",toJson n.toString),
      ("proof_identical",toJson (declared.value? true == c.value? true))]
    if sameDeclaration declared c then cachedReplicas := cachedReplicas.push row
    else duplicateOwners := duplicateOwners.push row
   else if !sameDeclaration declared c then
    duplicateOwners := duplicateOwners.push (Json.mkObj [("name",toJson declared.name.toString),("current",toJson n.toString),("reason",toJson "serialized declaration differs from selected owner")])
   owners := owners.insert declared.name n
   let refs := referenceNames c
   for dep in refs do
    edges := edges + 1
    if (env.checked.get.find? dep).isNone then
     dangling := dangling.push (Json.mkObj [("parent",toJson c.name.toString),("missing",toJson dep.toString)])
  let loaderImports := data.imports.map (fun i => i.module.toString)
  let imports := canonicalImports loaderImports
  let importMatch := match expected[n.toString]? with
   | some baseline => imports == baseline
   | none => false
  if !dangling.isEmpty || !duplicateOwners.isEmpty || !importMatch then failed := true
  out.putStrLn (Json.mkObj [("module",toJson n.toString), ("imports",toJson imports),
   ("loader_imports",toJson loaderImports), ("imports_match",toJson importMatch), ("dangling",toJson dangling), ("duplicate_owners",toJson duplicateOwners), ("cached_replicas",toJson cachedReplicas),
   ("declarations",toJson data.constants.size), ("edges",toJson edges)]).compress
 return failed
end NNO_Scan

/-- Standalone runtime avoids restoring a pre-initialization command environment. -/
unsafe def main (args : List String) : IO UInt32 := do
  NFA_MemoryLimit.set
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let mode := args.headD "small"
  let (modules, roots) := if mode == "scan" then (#[`NNO_StatementChecks], #[]) else (#[], #[])
  let env ← importModules (modules.map fun n => ({module := n, importAll := true} : Import))
    {} (loadExts := true) (level := .private)
  if mode == "scan" || mode == "queryscan" then
    let mut expected : Std.HashMap String (Array String) := {}
    for line in ← IO.FS.lines (if mode == "queryscan" then "NFN_QUERY_EXPECTED_IMPORTS.jsonl" else "NNO_EXPECTED_IMPORTS.jsonl") do
      let j ← IO.ofExcept (Json.parse line)
      expected := expected.insert (← IO.ofExcept (j.getObjValAs? String "module"))
        (← IO.ofExcept (j.getObjValAs? (Array String) "imports"))
    let failed ← NNO_Scan.loadedScan env (if mode == "queryscan" then "NFN_QUERY_LOADED_scan.jsonl" else "NNO_LOADED_scan.jsonl") expected
    IO.println (if failed then "NFN_SCAN_FAILED" else "NFN_SCAN_ZERO_DANGLING")
    return if failed then 1 else 0
  let ctx : Command.Context := {
    fileName := "NEP_Driver"
    fileMap := FileMap.ofString ""
    snap? := none
    cancelTk? := none
  }
  let action : CommandElabM Bool := do
    let mut failed := false
    for root in roots do
      try
        elabCommand (← `(command| #print axioms $(mkIdent root)))
        NEP.audit root ("NEP_" ++ mode ++ "_" ++ root.toString)
      catch e =>
        logError e.toMessageData
        failed := true
    return failed
  let result ← ((action.run ctx).run (Command.mkState env)).toBaseIO
  match result with
  | .error e =>
    IO.eprintln (← e.toMessageData.toString)
    return 2
  | .ok (failed, state) =>
    for msg in state.messages.toList do IO.println (← msg.data.toString)
    return if failed then 1 else 0
