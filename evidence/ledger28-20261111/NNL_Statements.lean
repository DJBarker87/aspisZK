import NNL_COMBINED_IMPORT
import Lean
open AspisR1
#print axioms NNL_Domains.exact094
#print axioms NNL_Domains.exact328
#print axioms NNL_Domains.domain094
#print axioms NNL_Domains.domain328
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

open AspisR1
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
