import NNL_COMBINED_IMPORT
import Lean
set_option autoImplicit false
noncomputable section
namespace NNL_Statements
open AspisR1

theorem exact094 : RSL.TX1_094.RowSpec_094 LIB_FullInstances.VL LIB_FullInstances.P
 NNG_ProducerFull094.producer := NNG_Candidate094.candidate

theorem exact328 : RSL.TX1_328.RowSpec_328 LIB_FullInstances.VL LIB_FullInstances.P
 NNG_Producer328.producer := NNG_Candidate328.candidate

theorem domain094 (a : RSL.TX1_094.Args LIB_Instances.VL) (obs : RSL.Observer) :
 RSL.TX1_094.Domain LIB_Instances.VL a obs a.public_ =
 (obs = none ∧ LIB_Instances.VL.publicDom a.public_ ∧ a.public_bytes.length = 1880) := rfl

theorem domain328 (a : RSL.TX1_094.Args LIB_Instances.VL) :
 RSL.TX1_328.Domain LIB_Instances.VL a =
 (LIB_Instances.VL.publicDom a.public_ ∧ a.public_bytes.length = 1880) := rfl

#print axioms exact094
#print axioms exact328
#print axioms domain094
#print axioms domain328
#print NNG_Candidate094.candidate
#print NNG_Candidate328.candidate
#print NNG_ProducerFull094.producer
#print NNG_Producer328.producer
#print NNG_Child328.original
#print NNG_TotalParse094.prepare_domain
#print NNG_P1880Discharge.decoder
#print RSL.TX1_345.p1880_of_decode
#print RSL.TX1_094.r4_of_scan
#print LIB_FullInstances.library
#print LIB_ParseShapeTotal.source
#print axioms NNG_ProducerFull094.source
#print axioms NNG_Tree328.source
#print axioms NNG_Native328.source
#print axioms NNG_TotalParse094.prepare_domain
#print axioms NNG_P1880Discharge.decoder
#print axioms LIB_ParseShapeTotal.source
end NNL_Statements
open Lean Elab Command
set_option pp.all true
run_cmd do
 let manifest ← IO.ofExcept (Json.parse (← IO.FS.readFile "NNL_AUDIT_ROOTS.json"))
 let roots ← IO.ofExcept (manifest.getObjValAs? (Array String) "roots")
 let env := (← getEnv).setExporting false
 for root in roots do
  let declName := root.toName
  let some c := env.find? declName | throwError "missing required root {root}"
  let some idx := env.getModuleIdxFor? declName | throwError "missing owner {root}"
  let statement ← liftTermElabM (PrettyPrinter.ppExpr c.type)
  let row := Json.mkObj [("root",toJson root),("owner_module",toJson env.header.moduleNames[idx]!.toString),("obligation_statement",toJson statement.pretty)]
  logInfo m!"NNL_OWNER {row.compress}"
