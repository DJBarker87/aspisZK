import Lean
import R0P.LaneMap
import R0P.CopyInputLinks
import R0P.Extraction
import R0P.SemAssembly
import R1UnifiedSamplerPublic
import R1PublicFieldBlockCodec
import R1PublicIndexCodec
import R1PublicIndexListCodec

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `R0P.LaneMap, `R0P.CopyInputLinks, `R0P.Extraction, `R0P.SemAssembly, `R1UnifiedSamplerPublic, `R1PublicFieldBlockCodec, `R1PublicIndexCodec, `R1PublicIndexListCodec ]
  for i in [:env.header.modules.size] do
    let owner := env.header.modules[i]!.module
    let data := env.header.moduleData[i]!
    logInfo m!"RPZ_IMPORTS {(Json.mkObj [("module", toJson owner.toString), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  let mut count : Nat := 0
  for (n, c) in env.toKernelEnv.constants.toList do
    if let some mi := env.getModuleIdxFor? n then
      let owner := env.header.modules[mi.toNat]!.module
      if c.isAxiom then
        logInfo m!"RPZ_AXIOM {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString)]).compress}"
      if selected.contains owner && n.hash.toNat % 1 == 0 then
        let axs ← collectAxioms n
        logInfo m!"RPZ_DECL {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("axioms", toJson (axs.map Name.toString))]).compress}"
        elabCommand (← `(#print axioms $(mkIdent n)))
        count := count + 1
  logInfo m!"RPZ_AUDIT_COMPLETE declarations={count} modules={selected.size}"
