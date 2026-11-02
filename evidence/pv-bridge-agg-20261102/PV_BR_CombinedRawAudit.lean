import PV_BR_FixtureConsumer
import Lean

open Lean Elab Command

namespace NDP

-- No use of collectAxioms' imported summaries: walk actual kernel bodies.
def audit (root : Name) (stem : String) : CommandElabM Unit := do
  let env := (← getEnv).setExporting false
  let some rootIdx := env.getModuleIdxFor? root | throwError "root module missing"
  let rootModule := env.header.modules[rootIdx]!.module
  let mut modules : NameMap (Array Name) := {}
  for i in [:env.header.modules.size] do
    modules := modules.insert env.header.modules[i]!.module
      (env.header.moduleData[i]!.imports.map (·.module))
  let mut todo := #[rootModule]
  let mut closure : NameSet := ({} : NameSet).insert rootModule
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    let some imports := modules.find? n | throwError "missing module {n}"
    for dep in imports do
      if !closure.contains dep then
        closure := closure.insert dep
        todo := todo.push dep
  let mut pending := #[root]
  let mut seen : NameSet := ({} : NameSet).insert root
  let mut edges : Nat := 0
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    let some c := env.checked.get.find? n | throwError "missing reachable constant {n}"
    let mut refs := c.type.getUsedConstants ++
      (((c.value? true).map Expr.getUsedConstants).getD #[])
    if let .inductInfo v := c then refs := refs ++ v.ctors.toArray
    edges := edges + refs.size
    for dep in refs do
      if !seen.contains dep then
        seen := seen.insert dep
        pending := pending.push dep
  let reachable := seen.toArray.qsort Name.lt
  liftIO <| IO.FS.writeFile (stem ++ "_REACHABLE.txt")
    (String.intercalate "\n" (reachable.toList.map Name.toString) ++ "\n")
  let mut allAxioms : NameSet := {}
  let mut rootAxioms : Array String := #[]
  for (n,c) in env.toKernelEnv.constants.toList do
    if c.isAxiom then
      allAxioms := allAxioms.insert n
      let some idx := env.getModuleIdxFor? n | throwError "axiom module missing {n}"
      let m := env.header.modules[idx]!.module
      let inClosure := closure.contains m
      if seen.contains n then rootAxioms := rootAxioms.push n.toString
      let pretty ← liftTermElabM <| Meta.ppExpr c.type
      logInfo m!"NDP_AXIOM {(Json.mkObj [
        ("name", toJson n.toString), ("module", toJson m.toString),
        ("level_params", toJson (c.levelParams.map Name.toString)),
        ("type", toJson pretty.pretty), ("type_expr", toJson (repr c.type).pretty),
        ("in_root_import_closure", toJson inClosure),
        ("reachable", toJson (seen.contains n))]).compress}"
  -- Independently check each loaded module's serialized declaration table.
  let mut serializedAxioms : NameSet := {}
  for i in [:env.header.modules.size] do
    let m := env.header.modules[i]!.module
    let data := env.header.moduleData[i]!
    for c in data.constants do
      if c.isAxiom then
        serializedAxioms := serializedAxioms.insert c.name
        unless allAxioms.contains c.name do
          throwError "serialized axiom absent from kernel enumeration: {m}: {c.name}"
    logInfo m!"NDP_MODULE {(Json.mkObj [("module", toJson m.toString),
      ("imports", toJson (data.imports.map (·.module.toString))),
      ("in_root_import_closure", toJson (closure.contains m))]).compress}"
  for n in allAxioms.toArray do
    unless serializedAxioms.contains n do
      throwError "kernel axiom absent from serialized enumeration: {n}"
  let reported ← collectAxioms root
  let walked := rootAxioms.qsort (· < ·)
  let reported := (reported.map Name.toString).qsort (· < ·)
  unless walked == reported do
    throwError "raw graph disagrees with collectAxioms: {walked} vs {reported}"
  logInfo m!"NDP_RESULT {(Json.mkObj [("root", toJson root.toString),
    ("root_module", toJson rootModule.toString), ("closure_modules", toJson closure.size),
    ("loaded_modules", toJson env.header.modules.size),
    ("reachable_constants", toJson reachable.size), ("edges_scanned", toJson edges),
    ("all_loaded_axioms", toJson allAxioms.size),
    ("serialized_axioms", toJson serializedAxioms.size),
    ("walked_axioms", toJson walked), ("collect_axioms", toJson reported)]).compress}"
  logInfo "NDP_AUDIT_COMPLETE"

end NDP

run_cmd NDP.audit `PV_EVH_FixtureConsumer.deployedInstance "audit-00"
#print axioms PV_EVH_FixtureConsumer.deployedInstance
run_cmd NDP.audit `PV_EVH_FixtureConsumer.instance_nonvacuity "audit-01"
#print axioms PV_EVH_FixtureConsumer.instance_nonvacuity
run_cmd NDP.audit `PV_EVH_FixtureConsumer.public_fibre "audit-02"
#print axioms PV_EVH_FixtureConsumer.public_fibre
run_cmd NDP.audit `PV_EVH_FixtureConsumer.two_transaction_nonvacuity "audit-03"
#print axioms PV_EVH_FixtureConsumer.two_transaction_nonvacuity
run_cmd NDP.audit `PV_BR_Transport.payment_left_inverse "audit-04"
#print axioms PV_BR_Transport.payment_left_inverse
run_cmd NDP.audit `PV_BR_Transport.payment_right_inverse "audit-05"
#print axioms PV_BR_Transport.payment_right_inverse
run_cmd NDP.audit `PV_BR_Transport.payment_discriminant "audit-06"
#print axioms PV_BR_Transport.payment_discriminant
run_cmd NDP.audit `PV_BR_Transport.payment_injective "audit-07"
#print axioms PV_BR_Transport.payment_injective
run_cmd NDP.audit `PV_BR_Transport.tree_left_inverse "audit-08"
#print axioms PV_BR_Transport.tree_left_inverse
run_cmd NDP.audit `PV_BR_Transport.tree_right_inverse "audit-09"
#print axioms PV_BR_Transport.tree_right_inverse
run_cmd NDP.audit `PV_BR_Transport.tree_discriminant "audit-10"
#print axioms PV_BR_Transport.tree_discriminant
run_cmd NDP.audit `PV_BR_Transport.tree_injective "audit-11"
#print axioms PV_BR_Transport.tree_injective
run_cmd NDP.audit `PV_BR_Transport.verifier_retraction "audit-12"
#print axioms PV_BR_Transport.verifier_retraction
run_cmd NDP.audit `PV_BR_Transport.verifier_join_split "audit-13"
#print axioms PV_BR_Transport.verifier_join_split
run_cmd NDP.audit `PV_BR_Transport.verifier_split_join "audit-14"
#print axioms PV_BR_Transport.verifier_split_join
run_cmd NDP.audit `PV_BR_Transport.verifier_embedding_injective "audit-15"
#print axioms PV_BR_Transport.verifier_embedding_injective
run_cmd NDP.audit `PV_BR_Transport.verifier_discriminant "audit-16"
#print axioms PV_BR_Transport.verifier_discriminant
run_cmd NDP.audit `PV_BR_Transport.mapCoreError_inverse "audit-17"
#print axioms PV_BR_Transport.mapCoreError_inverse
run_cmd NDP.audit `PV_BR_Transport.payment_result_transport "audit-18"
#print axioms PV_BR_Transport.payment_result_transport
run_cmd NDP.audit `PV_BR_Transport.tree_result_transport "audit-19"
#print axioms PV_BR_Transport.tree_result_transport
run_cmd NDP.audit `PV_BR_AdmissionTransport.prover_run_roundtrip "audit-20"
#print axioms PV_BR_AdmissionTransport.prover_run_roundtrip
run_cmd NDP.audit `PV_BR_AdmissionTransport.from_to "audit-21"
#print axioms PV_BR_AdmissionTransport.from_to
run_cmd NDP.audit `PV_BR_AdmissionTransport.to_from "audit-22"
#print axioms PV_BR_AdmissionTransport.to_from
run_cmd NDP.audit `PV_BR_AdmissionTransport.mapRunError_inverse "audit-23"
#print axioms PV_BR_AdmissionTransport.mapRunError_inverse
run_cmd NDP.audit `PV_BR_AdmissionTransport.mapRunError_success "audit-24"
#print axioms PV_BR_AdmissionTransport.mapRunError_success
run_cmd NDP.audit `PV_BR_AdmissionTransport.validateCommon_roundtrip "audit-25"
#print axioms PV_BR_AdmissionTransport.validateCommon_roundtrip
run_cmd NDP.audit `PV_BR_AdmissionTransport.validateCommon_success "audit-26"
#print axioms PV_BR_AdmissionTransport.validateCommon_success
run_cmd NDP.audit `R1Z.PrivacyR1HeadlineDeployedReal.privacy_headline_deployed "audit-27"
#print axioms R1Z.PrivacyR1HeadlineDeployedReal.privacy_headline_deployed
run_cmd NDP.audit `R1Z.PrivacyR1HeadlineDeployedEvents.privacy_headline_deployed_events "audit-28"
#print axioms R1Z.PrivacyR1HeadlineDeployedEvents.privacy_headline_deployed_events
run_cmd NDP.audit `R1Z.PV_RJ4IDB_CallerLive.caller_witness "audit-29"
#print axioms R1Z.PV_RJ4IDB_CallerLive.caller_witness
run_cmd NDP.audit `AspisR1.NDR_CombinedAudit.sourceOnHeadline "audit-30"
#print axioms AspisR1.NDR_CombinedAudit.sourceOnHeadline
