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
#print axioms LIB_FullInstances.canonical
#print axioms LIB_FullInstances.deployed_exact
#print axioms LIB_FullInstances.pool_exact
#print axioms LIB_FullInstances.prepared_exact
#print axioms LIB_FullInstances.statement_exact
#print axioms LIB_FullInstances.tas064
#print axioms LIB_FullInstances.tas213
#print axioms LIB_FullInstances.tas217
#print axioms LIB_FullInstances.tas221
#print axioms LIB_FullInstances.tas233
#print axioms LIB_FullInstances.tas234
#print axioms LIB_FullInstances.tas240
#print axioms LIB_FullInstances.tas241
#print axioms LIB_FullInstances.tas242
#print axioms LIB_FullInstances.v0_exact
#print axioms LIB_FullInstances.vl_exact
#print axioms LIB_ParseShape094.empty_reference
#print axioms LIB_ParseShape094.rejected
#print axioms LIB_ParseShape094.width_not_required
#print axioms LIB_ParseShapeTotal.closed086
#print axioms LIB_ParseShapeTotal.domain
#print axioms LIB_ParseShapeTotal.frozen_wrong_length
#print axioms LIB_ParseShapeTotal.functional
#print axioms LIB_ParseShapeTotal.graph
#print axioms LIB_ParseShapeTotal.rejected
#print axioms LIB_ParseShapeTotal.returns
#print axioms LIB_ParseShapeTotal.source
#print axioms LIB_ParseShapeTotal.wrong_length
#print axioms LIB_ParseShapeTotal.wrong_length_native
#print axioms LIB_VTx1A.parseShape_domain
#print axioms LIB_VTx1A.parseShape_functional
#print axioms RSL.TX1_094.domain_needs_P1880
#print axioms RSL.TX1_094.rejects_constErr
#print axioms RSL.TX1_328.ref_admits_abort
#print axioms RSL.TX1_328.rejects_silentRet
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
